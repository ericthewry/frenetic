open Core
open Fdd
open Syntax
open Semantics
       
exception Non_local = Syntax.Non_local
module FDD = Local_compiler.FDD
module Interp = Local_compiler.Interp
module OpenFlow = Frenetic_kernel.OpenFlow
module Util = Frenetic_kernel.Util
module Par = Action.Par
module Seq = Action.Seq
(*==========================================================================*)
(* GLOBAL COMPILATION                                                       *)
(*==========================================================================*)


(** internal policy representation that allows to inject fdds into policies, and
    uses DUP's instead of links. *)
module Pol = struct

  type t =
    | Filter of pred
    | Mod of header_val
    | Union of t * t
    | Seq of t * t
    | Star of t
    | Dup (** we can handle all of NetKAT *)
    | FDD of FDD.t * FDD.t (** FDD injection. E and D matrix. *)


  let drop = Filter False
  let id = Filter True

  let mk_filter pred = Filter pred
  let mk_mod hv = Mod hv

  let mk_union pol1 pol2 =
    match pol1, pol2 with
    | Filter False, _ -> pol2
    | _, Filter False -> pol1
    | _ -> Union (pol1,pol2)

  let mk_seq pol1 pol2 =
    match pol1, pol2 with
    | Filter True, _ -> pol2
    | _, Filter True -> pol1
    | Filter False, _ | _, Filter False -> drop
    | _ -> Seq (pol1,pol2)

  let mk_star pol =
    match pol with
    | Filter True | Filter False -> id
    | Star _ -> pol
    | _ -> Star(pol)

  let mk_fdd e d =
    if FDD.equal e FDD.drop && FDD.equal d FDD.drop then drop
    else FDD (e, d)

  let mk_big_union = List.fold ~init:drop ~f:mk_union
  let mk_big_seq = List.fold ~init:id ~f:mk_seq

  let match_loc sw pt =
    let t1 = Test (Switch sw) in
    let t2 = Test (Location (Physical pt)) in
    Optimize.mk_and t1 t2
  let match_vloc sw pt =
    let t1 = Test (VSwitch sw) in
    let t2 = Test (VPort pt) in
    Optimize.mk_and t1 t2

  let filter_loc sw pt = match_loc sw pt |> mk_filter
  let filter_vloc sw pt = match_vloc sw pt |> mk_filter

  let rec of_pol (ing : Syntax.pred option) (pol : Syntax.policy) : t =
    match pol with
    | Filter a -> Filter a
    | Mod hv -> Mod hv
    | Union (p,q) -> Union (of_pol ing p, of_pol ing q)
    | Seq (p,q) -> Seq (of_pol ing p, of_pol ing q)
    | Star p -> Star (of_pol ing p)
    | Link (s1,p1,s2,p2) ->
      let link = mk_seq (mk_mod (Switch s2)) (mk_mod (Location (Physical p2))) in
      let post_link = match ing with
        | None -> filter_loc s2 p2
        | Some ing ->
          Optimize.(mk_and (Test (Switch s2)) (mk_not ing))
          |> mk_filter in
      mk_big_seq [filter_loc s1 p1; Dup; link; Dup; post_link]
    (*ingress Dup is commented out for EdgeOF*)
    | VLink (s1,p1,s2,p2) ->
      let link = mk_seq (mk_mod (VSwitch s2)) (mk_mod (VPort p2)) in
      let post_link = match ing with
        | None -> filter_vloc s2 p2
        | Some ing ->
          Optimize.(mk_and (Test (VSwitch s2)) (mk_not ing))
          |> mk_filter in
      mk_big_seq [filter_vloc s1 p1; Dup; link; Dup; post_link]
    | Let _ -> failwith "meta fields not supported by global compiler yet"
    | Dup -> Dup
end



(** Symbolic NetKAT Automata (intermediate representation of global compiler) *)
module Automaton = struct

  (* state id tables: id |-> 'a *)
  module Tbl = Int64.Table

  (* untable (inverse table) *)
  module Untbl = FDD.BinTbl

  (* (hashable) state id (= int64) sets *)
  module S = struct
    module S = struct
      include Set.Make(Int64)
      let hash_fold_t state x = [%hash_fold: Int64.t list] state (to_list x)
      let hash = Ppx_hash_lib.Std.Hash.run hash_fold_t
    end
    include Hashable.Make(S)
    include S
  end

  (* main data structure of symbolic NetKAT automaton *)
  type t =
    { states : (FDD.t * FDD.t) Tbl.t;
      has_state : int64 Untbl.t;
      mutable source : int64;
      mutable nextState : int64 }

  (* lazy intermediate presentation to avoid compiling unreachable automata states *)
  type t0 =
    { states : (FDD.t * FDD.t) Lazy.t Tbl.t;
      source : int64;
      mutable nextState : int64 }

  let create_t0 () : t0 =
    let states = Tbl.create () ~size:100 in
    let source = 0L in
    { states; source; nextState = Int64.(source + 1L) }

  let create_t () : t =
    let states = Tbl.create () ~size:100 in
    let has_state = Untbl.create () ~size:100 in
    let source = 0L in
    { states; has_state; source; nextState = Int64.(source + 1L) }

  let mk_state_t0 (automaton : t0) : int64 =
    let id = automaton.nextState in
    automaton.nextState <- Int64.(id + 1L);
    id

  let mk_state_t (automaton : t) : int64 =
    let id = automaton.nextState in
    automaton.nextState <- Int64.(id + 1L);
    id

  let add_to_t (automaton : t) (state : (FDD.t * FDD.t)) : int64 =
    match Untbl.find automaton.has_state state with
    | Some k -> k
    | None ->
      let k = mk_state_t automaton in
      Tbl.add_exn automaton.states ~key:k ~data:state;
      Untbl.add_exn automaton.has_state ~key:state ~data:k;
      k

  let add_to_t_with_id (automaton : t) (state : (FDD.t * FDD.t)) (id : int64) : unit = begin
      assert (not (Tbl.mem automaton.states id));
      Tbl.add_exn automaton.states ~key:id ~data:state;
      Untbl.set automaton.has_state ~key:state ~data:id;
    end

  let map_reachable ?(order = `Pre) (automaton : t)
    ~(f: int64 -> (FDD.t * FDD.t) -> (FDD.t * FDD.t)) : unit =
    let rec loop seen (id : int64) =
      if S.mem seen id then seen else
        let seen = S.add seen id in
        let state = Tbl.find_exn automaton.states id in
        let this seen =
          let state = f id state in
          Tbl.set automaton.states ~key:id ~data:state; (seen, state) in
        let that (seen, (_,d)) = Set.fold (FDD.conts d) ~init:seen ~f:loop in
        match order with
        | `Pre -> seen |> this |> that
        | `Post -> (seen, state) |> that |> this |> fst
    in
    loop S.empty automaton.source |> ignore

  let fold_reachable ?(order = `Pre) (automaton : t) ~(init : 'a)
    ~(f: 'a -> int64 -> (FDD.t * FDD.t) -> 'a) =
    let rec loop (acc, seen) (id : int64) =
      if S.mem seen id then (acc, seen) else
        let seen = S.add seen id in
        let (_,d) as state = Tbl.find_exn automaton.states id in
        let this (acc, seen) = (f acc id state, seen) in
        let that (acc, seen) = Set.fold (FDD.conts d) ~init:(acc, seen) ~f:loop in
        match order with
        | `Pre -> (acc, seen) |> this |> that
        | `Post -> (acc, seen) |> that |> this
    in
    loop (init, S.empty) automaton.source |> fst

  let iter_reachable ?(order = `Pre) (automaton : t) ~(f: int64 -> (FDD.t * FDD.t) -> unit) : unit =
    fold_reachable automaton ~order ~init:() ~f:(fun _ -> f)

  let t_of_t0' (automaton : t0) =
    let t = create_t () in
    let rec add id =
      if not (Tbl.mem t.states id) then
        let _ = t.nextState <- max t.nextState Int64.(id + 1L) in
        let (_,d) as state = Lazy.force (Tbl.find_exn automaton.states id) in
        Tbl.add_exn t.states ~key:id ~data:state;
        Set.iter (FDD.conts d) ~f:add
    in
    add automaton.source;
    t.source <- automaton.source;
    t

  let lex_sort (t0 : t0) =
    let rec loop acc stateId =
      if List.mem ~equal:(=) acc stateId then acc else
      let init = stateId :: acc in
      let (_,d) = Lazy.force (Tbl.find_exn t0.states stateId) in
      Set.fold (FDD.conts d) ~init ~f:loop
    in
    loop [] t0.source

  let t_of_t0 ?(cheap_minimize=true) (t0 : t0) =
    if not cheap_minimize then t_of_t0' t0 else
    let t = create_t () in
    (* table that maps old ids to new ids *)
    let newId = Int64.Table.create () ~size:100 in
    lex_sort t0
    |> List.iter ~f:(fun id ->
        let (e,d) = Lazy.force (Tbl.find_exn t0.states id) in
        (* SJS: even though we are traversing the graph in reverse-lexiographic order,
           a node may be visited prior to one of its sucessors because there may be cylces *)
        let d = FDD.map_conts d ~f:(Tbl.find_or_add newId ~default:(fun () -> mk_state_t t)) in
        (* check if new id was already assigned *)
        match Tbl.find newId id with
        | None ->
          let new_id = add_to_t t (e,d) in
          Tbl.add_exn newId ~key:id ~data:new_id
        | Some new_id ->
          add_to_t_with_id t (e,d) new_id
      );
    t.source <- Tbl.find_exn newId t0.source;
    t

  (* classic powerset construction, performed on symbolic automaton *)
  let determinize (automaton : t) : unit =
    (* table of type : int set -> int *)
    let tbl : int64 S.Table.t = S.Table.create () ~size:10 in
    (* table of type : int -> int set *)
    let untbl : S.t Int64.Table.t = Int64.Table.create () ~size:10 in
    let unmerge k = Int64.Table.find untbl k |> Option.value ~default:(S.singleton k) in
    let merge ks =
      let () = assert Int.(S.length ks > 1) in
      let ks = S.fold ks ~init:S.empty ~f:(fun acc k -> S.union acc (unmerge k)) in
      match S.Table.find tbl ks with
      | Some k -> k
      | None ->
        let (es, ds) =
          S.to_list ks
          |> List.map ~f:(Tbl.find_exn automaton.states)
          |> List.unzip in
        let fdd = (FDD.big_union es, FDD.big_union ds) in
        let k = add_to_t automaton fdd in
        S.Table.add_exn tbl ~key:ks ~data:k;
        (* k may not be fresh, since there could have been an FDD equvialent to fdd
           present in the automaton already; therefore, simply ignore warning *)
        ignore (Int64.Table.add untbl ~key:k ~data:ks);
        k
    in
    let determinize_action par =
      par
      |> Action.Par.to_list
      |> List.sort ~compare:Action.Seq.compare_mod_k
      |> List.group ~break:(fun s1 s2 -> not (Action.Seq.equal_mod_k s1 s2))
      |> List.map ~f:(function
        | [seq] -> seq
        | group ->
          let ks =
            List.map group ~f:(fun s -> Action.Seq.find_exn s K |> Value.to_int64_exn)
            |> S.of_list
          in
          let k = merge ks in
          List.hd_exn group |> Action.Seq.set ~key:K ~data:(Value.of_int64 k))
      |> Action.Par.of_list
    in
    let dedup_fdd = FDD.map_r ~f:determinize_action in
    map_reachable automaton ~order:`Pre ~f:(fun _ (e,d) -> (e, dedup_fdd d))

  (** symbolic antimirov derivatives *)
  let rec split_pol (automaton : t0) (pol: Pol.t) : FDD.t * FDD.t * ((int64 * Pol.t) list) =
    (* SJS: temporary hack *)
    let env = Field.Env.empty in
    match pol with
    | Filter pred -> (FDD.of_pred env pred, FDD.drop, [])
    | Mod hv -> (FDD.of_mod env hv, FDD.drop, [])
    | Union (p,q) ->
      let (e_p, d_p, k_p) = split_pol automaton p in
      let (e_q, d_q, k_q) = split_pol automaton q in
      let e = FDD.union e_p e_q in
      let d = FDD.union d_p d_q in
      let k = k_p @ k_q in
      (e, d, k)
    | Seq (p,q) ->
      (* TODO: short-circuit *)
      let (e_p, d_p, k_p) = split_pol automaton p in
      let (e_q, d_q, k_q) = split_pol automaton q in
      let e = FDD.seq e_p e_q in
      let d = FDD.union d_p (FDD.seq e_p d_q) in
      let q' = Pol.mk_fdd e_q d_q in
      let k = (List.map k_p ~f:(fun (id,p) -> (id, Pol.mk_seq p q'))) @ k_q in
      (e, d, k)
    | Star p ->
      let (e_p, d_p, k_p) = split_pol automaton p in
      let e = FDD.star e_p in
      let d = FDD.seq e d_p in
      let pol' = Pol.mk_fdd e d in
      let k = List.map k_p ~f:(fun (id,k) -> (id, Pol.mk_seq k pol')) in
      (e, d, k)
    | Dup ->
      let id = mk_state_t0 automaton in
      let e = FDD.drop in
      let d = FDD.mk_cont id in
      let k = [(id, Pol.id)] in
      (e, d, k)
    | FDD (e,d) -> (e,d,[])

  let rec add_policy (automaton : t0) (id, pol : int64 * Pol.t) : unit =
    let f () =
      let (e,d,k) = split_pol automaton pol in
      List.iter k ~f:(add_policy automaton);
      (e, d)
    in
    Tbl.add_exn automaton.states ~key:id ~data:(Lazy.from_fun f)

  let of_policy ?(dedup=true) ?ing ?(cheap_minimize=true) (pol : Syntax.policy) : t =
    let automaton = create_t0 () in
    let pol = Pol.of_pol ing pol in
    let () = add_policy automaton (automaton.source, pol) in
    let automaton = t_of_t0 ~cheap_minimize automaton in
    let () = if dedup then determinize automaton in
    automaton

  module Value = struct
    include Value
    module Set = Set.Make(Value)
  end

  module Field = struct
    include Field
    module Map = Map.Make(Field)
  end

  type cnstr =
    | Eq of Value.t
    | Neq of Value.Set.t

  type pred = cnstr Field.Map.t

  let pred_to_fdd pred =
    Map.fold pred ~init:FDD.id ~f:(fun ~key:f ~data:c acc ->
      match c with
      | Eq v -> FDD.cond (f,v) acc FDD.drop
      | Neq vs -> Set.fold vs ~init:acc ~f:(fun acc v ->
          FDD.cond (f,v) FDD.drop acc
        )
    )

  (** Compute the "reach" of each state, i.e. a boolean predicate phi_s such that
      a pk can be in state s iff it satisfies phi_s.
      Not to be confused with the "support" of a state, i.e. the predicate psi_s
      such that a pk in s produces some output iff it satisfies psi_s.

      We could compute this precisely, but for now a overapproximation will do.
  *)
  let reach (automaton : t) : (int64, FDD.t) Hashtbl.t =
    let reach = Int64.Table.create () in
    (** initialize reach to false *)
    List.iter (Hashtbl.keys automaton.states) ~f:(fun id ->
      Hashtbl.add_exn reach ~key:id ~data:FDD.drop);
    let rec go worklist =
      match worklist with | [] -> () | (pred, id)::worklist ->
      let phi = Hashtbl.find_exn reach id in
      let phi' = FDD.union phi (pred_to_fdd pred) in
      if not (FDD.equal phi phi') then
      Hashtbl.set reach ~key:id ~data:phi';
      let (_, d) = Hashtbl.find_exn automaton.states id in
      let conts = FDD.fold d
        ~f:(fun par ->
          Par.to_list par
          |> List.map ~f:(fun seq ->
            Seq.to_alist seq
            |> List.filter_map ~f:(function
              | Action.K, v -> None
              | Action.F f, v -> Some (f, Eq v)
              )
            |> Field.Map.of_alist_exn
            |> fun constr -> (constr, Seq.find_exn seq Action.K |> Value.to_int64_exn)
          )
        )
        ~g:(fun (f,v) tru fls ->
          let tru = Util.map_fst tru ~f:(fun tru ->
            Map.update tru f ~f:(function None -> Eq v | Some c -> c)) in
          let fls = Util.map_fst fls ~f:(fun fls ->
            Map.update fls f ~f:(function
            | None -> Neq (Value.Set.singleton v)
            | Some (Neq vs) -> Neq (Value.Set.add vs v)
            | Some eq -> eq))
          in
          tru @ fls
        )
        |> Util.map_fst ~f:(fun pred' -> Field.Map.merge pred pred' ~f:(fun ~key v ->
          match v with
          | `Left c | `Right c -> Some c
          | `Both (_, (Eq _ as c)) -> Some c
          | `Both (Neq vs, Neq vs') -> Some (Neq Set.(union vs vs'))
          | `Both (Eq _, Neq _) -> assert false
        ))
        |> Util.map_fst ~f:Field.(fun pred -> Map.remove (Map.remove pred VPort) VSwitch)
      in
      go (conts @ worklist)
    in
    go [(Field.Map.empty, automaton.source)];
    reach

  let pc_unused pc fdd =
    FDD.fold fdd
      ~f:Action.(Par.for_all ~f:(fun seq -> not (Seq.mem seq (F pc))))
      ~g:(fun (f,_) l r -> l && r && f<>pc)

  (** a physical location is a switch-port-pair *)
  type ploc = int64 * int64

  (** Assumes [automaton] is a bipartite automaton in which switch states and
      topology states alternate, with the start state being a switch state.
      Modifies automaton by skipping topology states and transitioning straight
      to the (unique) next switch states.

      In the process, creates a [loc_map] : State -> Ploc that maps a switch state
      to its physical location, and a [state_map] : Ploc -> State Set that maps
      a physical location to the set of states this location can be in.
    *)
  let skip_topo_states (automaton : t)
    : ((int64, ploc) Hashtbl.t * (ploc, Int64.Set.t) Hashtbl.t) =
    (* maps switch states to their physical locations *)
    let loc_map : (int64, ploc) Hashtbl.t = Int64.Table.create () in
    (* maps physical locations to set of states it can be in *)
    let state_map : (ploc, Int64.Set.t) Hashtbl.t = Hashtbl.Poly.create () in
    (* remove topology states and populate maps in the process *)
    map_reachable automaton ~order:`Pre ~f:(fun _ (e,d) ->
      let d = FDD.map_conts d ~f:(fun k ->
        match Tbl.find_exn automaton.states k |> snd |> FDD.unget with
        | Leaf par ->
          let seq = match Par.to_list par with
            | [seq] -> seq
            | _ -> failwith "malformed topology state"
          in
          begin match Action.(Seq.find seq (F Switch),
                              Seq.find seq (F Location),
                              Seq.find seq K) with
          | Some (Const sw), Some (Const pt), Some (Const k) ->
            Int64.Table.set loc_map ~key:k ~data:(sw,pt);
            Hashtbl.Poly.update state_map (sw,pt) ~f:(function
              | None -> Int64.Set.singleton k
              | Some ks -> Set.add ks k);
            k
          | _ -> failwith "malformed topology state"
          end
        | _ -> failwith "malformed topology state")
      in (e,d));
    (loc_map, state_map)

  let disjoint phi psi =
    FDD.(equal drop (seq phi psi))

  open Graph
  module G = Imperative.Graph.Abstract(Int64)
  module C = Coloring.Mark(G)

  let min_coloring g =
    let rec bin_search i j =
      if i = j then i else
      let k = i + (j-i)/2 in
      try C.coloring g k; bin_search i k with
      | _ -> bin_search (k+1) j
    in
    bin_search 1 (G.nb_vertex g)

  let merge_states (automaton : t) reach loc_map (state_map : (ploc, Int64.Set.t) Hashtbl.t)
    : (ploc, Int64.Set.t) Hashtbl.t =
    let fuse ploc states =
      let (e,d,phi) =
        Int64.Set.fold states ~init:FDD.(drop, drop, drop) ~f:(fun (e,d,phi) id ->
          let e',d' = Hashtbl.find_exn automaton.states id in
          let psi = Hashtbl.find_exn reach id in
          let e',d' = FDD.(seq psi e', seq psi d') in
          FDD.(union e e', union d d', union phi psi))
      in
      let id = add_to_t automaton (e,d) in
      Hashtbl.update reach id ~f:(function None -> phi | Some psi -> FDD.union phi psi);
      Hashtbl.set loc_map ~key:id ~data:ploc;
      map_reachable automaton ~order:`Pre ~f:(fun _ (e,d) ->
        let d = FDD.map_conts d ~f:(fun k -> if Set.mem states k then id else k) in
        (e,d)
      );
      id
    in
    let merge ~key:ploc ~data:states =
      let n = Set.length states in
      (* create contraint graph *)
      let g = G.create () in
      Set.iter states ~f:(fun i -> G.add_vertex g G.V.(create i));
      G.iter_vertex (fun i ->
        G.iter_vertex (fun j ->
          let ii = G.V.label i and jj = G.V.label j in
          if ii < jj && not (disjoint (Hashtbl.find_exn reach ii) (Hashtbl.find_exn reach jj)) then
            G.add_edge g i j
        ) g
      ) g;
      let k = min_coloring g in
      if k = n then states else begin
        printf "Found %d-coloring of %d states!\n" k n;
        let partition = Array.init k ~f:(fun _ -> Int64.Set.empty) in
        G.iter_vertex (fun v ->
          let i = G.V.label v in
          let c = G.Mark.get v - 1 in
          partition.(c) <- Set.add partition.(c) i
        ) g;
        Array.map partition ~f:(fuse ploc)
        |> Int64.Set.of_array
      end
    in
    Hashtbl.mapi state_map ~f:(merge)

  let to_local ~(pc : Field.t) (automaton : t) : FDD.t =
    let reach = reach automaton in
    let (loc_map, state_map) = skip_topo_states automaton in
    let state_map = merge_states automaton reach loc_map state_map in
    let state_map = Hashtbl.Poly.map state_map ~f:(fun states ->
      Set.to_list states
      |> List.mapi ~f:(fun i state -> (state, i))
      |> Int64.Map.of_alist_exn)
    in
    (** maps state ids to their pc-value, using loc_map and state_map for
        inspiration to allocate pc-values economically. Returns boolean indicating
        whether a state is unique to its location. *)
    let get_pc (id : int64) : (Value.t * bool) =
      let ploc = Int64.Table.find_exn loc_map id in
      let ploc_states = Hashtbl.Poly.find_exn state_map ploc in
      let index = Int64.Map.find_exn ploc_states id in
      (Value.of_int index, Map.length ploc_states = 1)
    in
    let pop_vlan = FDD.of_mod Field.Env.empty (Vlan 0xffff) in
    fold_reachable automaton ~init:FDD.drop ~f:(fun acc id (e,d) ->
      let _ = assert (pc_unused pc e && pc_unused pc d) in
      let d =
        FDD.map_r (Par.map ~f:(fun seq -> match Seq.find seq K with
          | None -> failwith "transition function must specify next state!"
          | Some k ->
            let k = Value.to_int64_exn k in
            let (pc_val, unique) = get_pc k in
            let seq = Seq.remove seq K in
            if unique then
              seq
            else
              Seq.set seq ~key:(F pc) ~data:pc_val
          ))
          d
      in
      let e =
        (* SJS: Vlan specific hack. Ideally, this should be more general *)
        if pc = Field.Vlan then
          FDD.seq e pop_vlan
        else
          e
      in
      let guard =
        if id = automaton.source then FDD.id else
        let (pc_val, unique) = get_pc id in
        if unique then FDD.id else
        FDD.atom (pc, pc_val) Action.one Action.zero in
      let fdd = FDD.seq guard (FDD.union e d) in
      FDD.union acc fdd)

  let to_dot (automaton : t) =
    let open Format in
    let buf = Buffer.create 200 in
    let fmt = formatter_of_buffer buf in
    let states = Hashtbl.map automaton.states ~f:(fun (e,d) -> FDD.union e d) in
    let state_lbl fmt = fprintf fmt "state_%Ld" in
    let fdd_lbl fmt fdd = fprintf fmt "fdd_%d" (fdd : FDD.t :> int) in
    let fdd_leaf_lbl fmt (i,fdd) = fprintf fmt "seq_%d_%d" (fdd : FDD.t :> int) i in

    (* remove unreachable states *)
    let reachable = fold_reachable automaton ~init:Int64.Set.empty
      ~f:(fun reachable id _ -> Int64.Set.add reachable id) in
    List.iter (Hashtbl.keys states) ~f:(fun id ->
      if not (Int64.Set.mem reachable id) then Hashtbl.remove states id);

    (* auxillary functions *)
    let rec do_states () =
      fprintf fmt "# put state nodes on top\n";
      fprintf fmt "{rank=source;";
      List.iter (Hashtbl.keys states) ~f:(fprintf fmt " %a" state_lbl);
      fprintf fmt ";}@\n";
      (* -- *)
      fprintf fmt "\n# mark start state\n";
      fprintf fmt "%a [style=bold, color=red, shape=octagon];@\n" state_lbl automaton.source;
      (* -- *)
      fprintf fmt "\n# connect state nodes to FDDs\n";
      Hashtbl.iteri states ~f:(fun ~key:id ~data:fdd ->
        fprintf fmt "%a -> %a;@\n" state_lbl id fdd_lbl fdd);
      (* -- *)
      fprintf fmt "\n# define FDDs\n";
      do_fdds Int.Set.empty (Hashtbl.data states)

    and do_fdds seen worklist =
      match worklist with
      | [] -> ()
      | fdd::worklist ->
        let uid = (fdd : FDD.t :> int) in
        if Set.mem seen uid then
          do_fdds seen worklist
        else
          do_node (Set.add seen uid) worklist fdd

    and do_node seen worklist fdd =
      match FDD.unget fdd with
      | Branch { test = f, v; tru; fls } ->
        fprintf fmt "%a [label=\"%s = %s\"];\n" fdd_lbl fdd (Field.to_string f) (Value.to_string v);
        fprintf fmt "%a -> %a;\n" fdd_lbl fdd fdd_lbl tru;
        fprintf fmt "%a -> %a [style=\"dashed\"];\n" fdd_lbl fdd fdd_lbl fls;
        do_fdds seen (tru::fls::worklist)
      | Leaf par ->
        fprintf fmt "subgraph cluster_%a {@\n" fdd_lbl fdd;
        fprintf fmt "\trank=sink;@\n";
        fprintf fmt "\t%a [shape = point];@\n" fdd_lbl fdd;
        let transitions = List.mapi (Action.Par.to_list par) ~f:(do_seq fdd) in
        fprintf fmt "}@\n";
        List.iter transitions ~f:(function
          | None -> ()
          | Some (s,t) ->
            fprintf fmt "%a -> %a [style=bold, color=blue];@\n" fdd_leaf_lbl s state_lbl t);
        do_fdds seen worklist

    and do_seq fdd (i: int) seq =
      let label = Action.Seq.to_string seq in
      fprintf fmt "\t%a [shape=box, label=\"%s\"];@\n" fdd_leaf_lbl (i,fdd) label;
      Option.map (Action.Seq.find seq K) ~f:(fun v ->
        ((i, fdd), Value.to_int64_exn v))

    in begin
      fprintf fmt "digraph automaton {@\n";
      do_states ();
      fprintf fmt "}@.";
      Buffer.contents buf
      end

         
  let render ?(format="pdf") ?(title="FDD") t =
    Frenetic_kernel.Util.show_dot ~format ~title (to_dot t)

  let fdd_trace_interp policy packet : (packet * (Syntax.location list)) list =
    (* Compute an automaton for the input policy *)
    let auto = of_policy ~dedup:true ~cheap_minimize:true policy in
    let rec interp is_phys (pkt, seen) (id : int64) : (packet * (Syntax.location list)) list =
      (* Printf.printf "\nSTATE: %s " (Int64.to_string id);
       * Printf.printf "Packet: Vlan %s EthSrc %s EthDst %s IPDst %s Port %s Switch %s\n" (Int.to_string pkt.headers.vlan) (Int64.to_string pkt.headers.ethSrc) (Int64.to_string pkt.headers.ethDst) (Int32.to_string pkt.headers.ipDst) (Int32.to_string ((fun (Physical port) -> port) pkt.headers.location)) (Int64.to_string pkt.switch); *)

      let seen' = S.add seen id in
      let (e,d) as state = Tbl.find_exn auto.states id in
      (* Printf.printf "E: %s\n" (FDD.to_string e); *)
      let epkts = Interp.eval pkt e in
      let dpkts =
        (* Printf.printf "D: %s\n" (FDD.to_string d); *)
        let restr_d = FDD.restrict (List.map(to_hvs pkt) ~f:Pattern.of_hv) d in
        PacketSet.fold (Interp.eval pkt restr_d) ~init:[] ~f:(fun acc dpkt ->
            let next_hops = FDD.conts restr_d in
            (* If there are no next hops then we're at the end of the trace *)
            if Int64.Set.is_empty next_hops then
              (* let () = Printf.printf "NO HOPS" in *)
              [(dpkt, [])]
            else
              Int64.Set.fold next_hops ~init:[] ~f:(fun acc next_hop ->
                  (* Printf.printf "K: %s\n" (Int64.to_string next_hop); *)
                  List.fold (interp (not is_phys) (dpkt, seen') next_hop) ~init:[]
                    ~f:(fun acc (final_packet, trace) ->
                      (* Printf.printf "TRACE : ";
                       * List.iter trace ~f:(fun (Physical p) -> Printf.printf " %s" (Int32.to_string p));
                       * Printf.printf "\n"; *)
                      let trace' = if is_phys then trace else dpkt.headers.location :: trace in
                      (final_packet, trace') :: acc
                    ) |> List.append acc
                ) |> List.append acc
          ) in
      PacketSet.fold epkts ~init:dpkts ~f:(fun acc epkt -> (epkt, []) :: acc)
    in
    interp false (packet, S.empty) auto.source

  type elt =
    | TrTest of bool * FDD.v
    | TrMod of FDD.v

  let getmod (e:elt) : (Field.t * Value.t) option =
    match e with
    | TrTest _ -> None
    | TrMod hv -> Some hv

  let string_of_elt (e:elt) : string =
    match e with
    | TrTest (b, (Switch, Const v)) -> (if b then "" else "NEG ") ^
                                         "Switch = " ^ Int64.to_string v
    | TrTest (b, (Location, Const v)) -> (if b then "" else "NEG ") ^
                                           "Location = " ^ Int64.to_string v
    | TrTest (b, (EthDst, Const v)) -> (if b then "" else "NEG ") ^
                                         "EthDst = " ^ Int64.to_string v
    | TrMod (Switch, Const v) -> "Switch := " ^ Int64.to_string v
    | TrMod (Location, Const v) -> "Location := " ^ Int64.to_string v
    | TrMod (EthDst, Const v) ->"EthDst := " ^ Int64.to_string v
    | _ -> failwith "Unsupported header"

  let mk_trmods action : elt list = List.map (Action.Par.to_hvs action) ~f:(fun hv -> TrMod hv)

  let mk_trtest b fv : elt =  TrTest (b, fv)

  let uncurry f (x,y) = f x y
                   
              
  (*Expand a single path into all paths through the automaton*)
  let rec expand_one_path (path: (int64 * FDD.t) list) : elt list list= 
    match path with
    | [] -> []
    | [(_,fdd)] ->
       List.map (FDD.paths fdd)
         ~f:(fun (test_list, action) ->
           List.fold test_list ~init:[]
             ~f:(fun acc (b, test) -> acc @ [mk_trtest b test] )
           @ mk_trmods action
         )
    | ((_,fdd)::(nextid,fdd')::fdds) ->
       List.fold (FDD.paths fdd) ~init:[]
         ~f:(fun accum (path, action) ->
           let trace = List.map path ~f:(fun (b, hv) -> mk_trtest b hv) @ mk_trmods action in
           
           match FDD.act_cont action with
           | None ->
              Printf.printf "CONTINUATION\n";
              trace :: accum
           | Some id -> (*if id = nextid then*)
              let () = Printf.printf "CONTINUATION\n" in
              let rec_paths = expand_one_path( (nextid, fdd') :: fdds )  in
                            (List.map ~f:(fun p -> trace @ p) rec_paths) @ accum
                         (*else accum*)
         )
      
  let eliminate head valu (cond: (bool * (Field.t * Value.t)) list) =
    let open Option in
    let optcons x l = Some (List.cons x l) in
    List.fold cond ~init:(Some []) ~f:(fun acc (b, (h,v)) ->
        if h <> head (*Skip irrelevant headers*)
        then acc >>= optcons (b, (h,v))
        else (*header is the same*)
          if b = (v = valu) then
            (* let () = Printf.printf "%s = %s elim\n" (Field.to_string h) (Value.to_string v) in *)
            acc (*Eliminate tautological conditions*)
          else None (*Trace is a contradiction *)
      )
      
  (*Expand paths through automaton to paths through FDDS*)
  let expand_paths paths : elt list list =
    let paths = List.fold paths ~init:[]
                  ~f:(fun acc p ->
                    Printf.printf "pathlength :: %d\n" (List.length p);
                    expand_one_path p @ acc)
    in
    Printf.printf "Expanded Paths: \n[\n";
    List.iter paths ~f:(fun path ->
        Printf.printf "\t[ ";
        List.iter path ~f:(fun e ->
            Printf.printf "%s," (string_of_elt e);
          );
        Printf.printf "],\n"
      );
    Printf.printf "]\n";
    paths

  (* Assume [prec] is sat *)
  let simplify_precondition prec : (bool * (Field.t * Value.t)) list = prec
    (* let (truths, falses) = List.partition_tf ~f:fst prec in
     * let member_of_truths f = List.fold truths ~init:false
     *                            ~f:(fun acc (b, (h,v)) ->
     *                              if h = f then true else acc ) in
     * let falses' = List.filter falses ~f:(fun (_, (h, _)) ->  member_of_truths h ) in
     * truths @ falses' *)

  (* a path is a list of tagged predicates and actions
   * predicate is a weakest precondition (expressed as a list of matches) to complete that path
   * trace is the list of port-assignments in that path
   * final packet is the result of running a packet matching the weakest precondition through the path
   *)
  let predicate_for_path (path : elt list) : ((bool * (Field.t * Value.t)) list) option =
    let open Option in 
    let rec loop rev_path cond =
      match rev_path with
      | [] -> Some cond
      | pred :: rev_path' ->
         match pred with
         | TrTest (b, tst) -> loop rev_path' ((b, tst) :: cond)
         | TrMod (header, value) ->
            match eliminate header value cond with
            | None -> None
            | Some cond' -> loop rev_path' cond'
    in
    loop (List.rev path) []
    
  let trace_for_path (path : elt list) : int64 list =
    List.fold path ~init:[] ~f:(fun accum tr ->
        match tr with
        | TrMod (Location, Const v) -> v :: accum
        | _  -> accum
      )
      
  (*PRE:: each header only appears once in precond *)
  let packet_satisfying (precond : (bool * (Field.t * Value.t)) list) =
    let precond_true = List.filter precond ~f:fst in
    let packet_sat_true = List.fold precond_true ~init:(make_packet ()) ~f:(fun pkt (b,(h,v)) ->
                              match v with
                              | Const res -> 
                                 (match h with
                                  | Field.Switch -> {pkt with switch = res }
                                  | Field.Location -> {pkt with headers = {pkt.headers with location = Physical (Int32.of_int64_exn res)}}
                                  | Field.Vlan -> {pkt with headers = {pkt.headers with vlan = Int.of_int64_exn res }}
                                  | Field.VlanPcp -> {pkt with headers = {pkt.headers with vlanPcp = Int.of_int64_exn res }}
                                  | Field.EthType -> {pkt with headers = {pkt.headers with ethType = Int.of_int64_exn res }}
                                  | Field.IPProto -> {pkt with headers = {pkt.headers with ipProto = Int.of_int64_exn res }}
                                  | Field.EthSrc -> {pkt with headers = {pkt.headers with ethSrc = res }}
                                  | Field.EthDst -> {pkt with headers = {pkt.headers with ethDst = res}}
                                  | Field.IP4Src -> {pkt with headers = {pkt.headers with ipSrc = Int32.of_int64_exn res }}
                                  | Field.IP4Dst -> {pkt with headers = {pkt.headers with ipDst = Int32.of_int64_exn res }}
                                  | Field.TCPSrcPort -> {pkt with headers = {pkt.headers with tcpSrcPort = Int.of_int64_exn res}}
                                  | Field.TCPDstPort -> {pkt with headers = {pkt.headers with tcpDstPort = Int.of_int64_exn res}}
                                  | _ -> failwith "Unsupported header field")
                              | _ -> failwith "unsupported value type"
                            ) in
    let precond_false = List.filter precond ~f:(fun p -> not (fst p)) in
    let packet_unsat_false = List.fold precond_false ~init:packet_sat_true ~f:(fun pkt (b, (h, v)) ->
                                 match v with
                                 | Const res ->
                                    (match h with
                                     | Field.Switch -> if pkt.switch = res
                                                       then {pkt with switch = Int64.(+) res 1L}
                                                       else pkt
                                     | Field.Location -> if pkt.headers.location = Physical (Int32.of_int64_exn res)
                                                         then {pkt with headers = {
                                                                  pkt.headers with
                                                                  location = Physical (Int32.(+) 1l (Int32.of_int64_exn res))}}
                                                         else pkt
                                     | Field.Vlan -> if pkt.headers.vlan = Int.of_int64_exn res
                                                     then {pkt with headers = {
                                                              pkt.headers with
                                                              vlan = Int.of_int64_exn res
                                                            }
                                                          }
                                                     else pkt
                                     | Field.VlanPcp -> if pkt.headers.vlanPcp = Int.of_int64_exn res
                                                        then {pkt with headers = {
                                                                 pkt.headers with
                                                                 vlanPcp = Int.of_int64_exn res
                                                               }
                                                             }
                                                        else pkt
                                     | Field.EthType -> if pkt.headers.ethType = Int.of_int64_exn res
                                                        then {pkt with headers = {
                                                                 pkt.headers with
                                                                 ethType = Int.of_int64_exn res
                                                               }
                                                             }
                                                        else pkt
                                     | Field.IPProto -> if pkt.headers.ipProto = Int.of_int64_exn res
                                                        then {pkt with headers = {
                                                                 pkt.headers with
                                                                 ipProto = Int.of_int64_exn res
                                                               }
                                                             }
                                                        else pkt
                                     | Field.EthSrc -> if pkt.headers.ethSrc = res
                                                       then {pkt with headers = {
                                                                pkt.headers with
                                                                ethSrc = res
                                                              }
                                                            }
                                                       else pkt
                                     | Field.EthDst -> if pkt.headers.ethDst = res
                                                       then {pkt with headers = {
                                                                pkt.headers with
                                                                ethDst= res
                                                              }
                                                            }
                                                       else pkt
                                     | Field.IP4Src -> if pkt.headers.ipSrc = Int32.of_int64_exn res
                                                       then {pkt with headers = {
                                                                pkt.headers with
                                                                ipSrc = Int32.of_int64_exn res
                                                              }
                                                            }
                                                       else pkt
                                     | Field.IP4Dst -> if pkt.headers.ipDst = Int32.of_int64_exn res
                                                       then {pkt with headers = {
                                                                pkt.headers with
                                                                ipDst = Int32.of_int64_exn res
                                                              }
                                                            }
                                                       else pkt
                                     | Field.TCPSrcPort -> if pkt.headers.tcpSrcPort = Int.of_int64_exn res
                                                           then {pkt with headers = {
                                                                    pkt.headers with
                                                                    tcpSrcPort = Int.of_int64_exn res
                                                                  }
                                                                }
                                                           else pkt
                                     | Field.TCPDstPort -> if pkt.headers.tcpDstPort = Int.of_int64_exn res
                                                           then {pkt with headers = {
                                                                    pkt.headers with
                                                                    tcpDstPort = Int.of_int64_exn res
                                                                  }
                                                                }
                                                           else pkt
                                     | _ -> failwith "unsupported field type"
                                                     
                                    )
                                 | _ -> failwith "unsupported value type"
                               ) in
    packet_unsat_false


  let to_syntax ((header, value) : (Field.t * Value.t)) : Syntax.header_val =
    match value with
    | Const v -> 
       (match header with
        | Field.Switch -> Syntax.Switch v
        | Field.Location -> Syntax.Location (Physical (Int32.of_int64_exn v))
        | Field.EthSrc -> Syntax.EthSrc v
        | Field.EthDst -> Syntax.EthDst v
        | Field.Vlan -> Syntax.Vlan (Int.of_int64_exn v)
        | Field.VlanPcp -> Syntax.VlanPcp (Int.of_int64_exn v)
        | Field.EthType -> Syntax.EthType (Int.of_int64_exn v)
        | Field.IPProto -> Syntax.IPProto (Int.of_int64_exn v)
        | Field.IP4Src -> Syntax.IP4Src (Int32.of_int64_exn v, 32l) (* Exact Matches Only *)
        | Field.IP4Dst -> Syntax.IP4Dst (Int32.of_int64_exn v, 32l)
        | Field.TCPSrcPort -> Syntax.TCPSrcPort (Int.of_int64_exn v)
        | Field.TCPDstPort -> Syntax.TCPDstPort (Int.of_int64_exn v)
        | _ -> failwith "unsupported header type"
       )
    | _ -> failwith "unsupported value type"


  let program_from_path path =
    List.fold path ~init:Syntax.id ~f:(fun prog tr ->
        match tr with
        | TrTest (true, (h,v)) -> Seq(Filter(Test(to_syntax (h,v))), prog)
        | TrTest (false,(h,v)) -> Seq(Filter(Neg (Test(to_syntax (h,v)))), prog)
        | TrMod (h,v) -> Seq( Mod(to_syntax(h,v)) , prog)
      )

  let rec subsumed f path : bool =
    match path with
    | [] -> false
    | ((x,_)::path') -> if f = x then true else subsumed f path'
    
  let mods_for_path (path : elt list) : (Field.t * Value.t) list =
    List.filter_map path ~f:getmod
    |> List.fold  ~init:[] ~f:(fun acc (h,v) -> if subsumed h acc
                                                then acc
                                                else (h, v)::acc)

  let rec contradictory pred : bool = 
    let rec contradicts f v pred =
      match pred with
      | [] -> false
      | (true, (f', v'))::pred' -> f = f' && v <> v' || contradicts f v pred'
      | (false, (f',v'))::pred' -> f = f' && v =  v' || contradicts f v pred'
    in
    match pred with
    | None -> true
    | Some [] -> false
    | Some ((b, (f,v))::pred') -> 
       if contradicts f v pred' then b else contradictory (Some pred')
                  
  let get_all_paths pol : ((((bool * (Field.t * Value.t)) list) option)
                           * (int64 list)
                           * (Field.t * Value.t) list) list =
    (* Get Automaton *)
    let auto = of_policy ~dedup:true ~cheap_minimize:true pol in
    render auto;

    (* Compute Paths *)
    let rec collect_all_paths count (curr_id:int64) seen (path:(int64 * FDD.t) list) : (int64 * FDD.t) list list =
      Printf.printf "recurse depth: %d\n" count;
      Printf.printf "[";
      List.iter path ~f:(fun (p,_) -> Printf.printf "%s," (Int64.to_string p));
      Printf.printf "\t%s]\n" (Int64.to_string curr_id);
      if S.mem seen curr_id then [[]] else
      let seen' = S.add seen curr_id in                        (* prevent loops *)
      let (e,d) as state = Tbl.find_exn auto.states curr_id in (* lookup current state*)
      let succs = FDD.conts d |> Int64.Set.elements in         (* compute successor Fdds*)
      let path_append x = path @ [(curr_id, x)] in             (* helper function to fdd to path *)

      Printf.printf "Epath_length: %d\n" (List.length (path_append e));
      
      (*Initialize with path that ends on e *)
      (* Recursively call on all of the successors *)
      let start = if e <> FDD.drop then [path_append e] else [] in
      let out = List.fold succs ~init:start ~f:(fun acc next_id ->
                    collect_all_paths (count+1) next_id seen' (path_append d) @ acc ) in
      List.iter out ~f:(fun p -> Printf.printf "outlength = %d\n" (List.length p));
      out
    in
    
    Printf.printf "COLLECTING PATHS\n";
    let ps = collect_all_paths 0 auto.source S.empty [] in
    let () = Printf.printf "--COLLECTED\n\nEXPANDING\n" in
    let eps = expand_paths ps in
    let () = Printf.printf "--EXPANDED\n" in
    List.filter_map eps ~f:(fun p ->
        let () = Printf.printf "Path [";
                 List.iter p (fun e -> Printf.printf " %s," (string_of_elt e));
                 Printf.printf "]\n"
        in
        let pred = predicate_for_path p in
        let () = Printf.printf "Pred [";
                 match pred with
                 | None -> Printf.printf "None\n";
                 | Some pred ->
                    List.iter pred (fun (b,(h,v)) ->
                     Printf.printf "(%B, (%s,%s))" b (Field.to_string h) (Value.to_string v));
                    Printf.printf "]\n" in
        let tr = trace_for_path p in
        let mds = mods_for_path p in
        if pred = None || tr = [] or mds = [] then None else
          if contradictory pred then
            None
          else Some (pred,
                     trace_for_path p,
                     mods_for_path p))
             
  (* Assume switches have no more than 32 ports, i.e. 5 bits for port id
   * only cannibalize the ethDst address for now *)
  let cannibalize_packet pkt trace : packet =
    let rec cannibalize_mac trace counter mac =
      match trace, counter with
      | [], 0 -> mac
      | _, 0 -> failwith "Packet trace is too long"
      | [], i -> cannibalize_mac trace (i-1) (Int64.shift_left mac 6)
      | (pt :: pts), i ->
         if pt > 31L then failwith "Port takes more than 5 bits" else
           let mac' = Int64.shift_left mac 6 |> Int64.(+) pt |> Int64.(+) 32L in
           cannibalize_mac pts (i-1) mac'
    in
    { pkt with headers = {
        pkt.headers with
        ethDst = cannibalize_mac trace 8 0L
      }
    }
                           

  let flow_from_packet ~flow:match_pkt ~action:act_pkt ~outport:next_hop ~match_inport:match_inport ~minimize:minimize : OpenFlow.flow =
    let open OpenFlow in
    let match_hvs = match_pkt.headers in
    let match_pat : Pattern.t =  {
        dlSrc     = Some match_hvs.ethSrc;
        dlDst     = Some match_hvs.ethDst;
        dlTyp     = Some match_hvs.ethType;
        dlVlan    = Some match_hvs.vlan;
        dlVlanPcp = Some match_hvs.vlanPcp;
        nwSrc     = Some (match_hvs.ipSrc, 32l);
        nwDst     = Some (match_hvs.ipDst, 32l);
        nwProto   = Some match_hvs.ipProto;
        tpSrc     = Some match_hvs.tcpSrcPort;
        tpDst     = Some match_hvs.tcpDstPort;
        inPort    = match match_hvs.location, match_inport with
                    | Physical inport, true -> Some inport
                    | _, _ -> None
                            
      } in
    let act_hvs = act_pkt.headers in
    let ethSrcAct = if minimize && act_hvs.ethSrc = match_hvs.ethSrc then [] else [SetEthSrc act_hvs.ethSrc |> Modify] in
    let ethDstAct = if minimize && act_hvs.ethDst = match_hvs.ethDst then [] else [SetEthDst act_hvs.ethDst |> Modify] in
    let vlanAct = if minimize && act_hvs.vlan = match_hvs.vlan then [] else [SetVlan (Some act_hvs.vlan) |> Modify] in
    let vlanPcpAct = if minimize && act_hvs.vlanPcp = match_hvs.vlanPcp then [] else [SetVlanPcp act_hvs.vlanPcp |> Modify] in
    let ethTypeAct = if minimize && act_hvs.ethType = match_hvs.ethType then [] else [SetEthTyp act_hvs.ethType |> Modify] in
    let ipProtoAct = if minimize && act_hvs.ipProto = match_hvs.ipProto then [] else [SetIPProto act_hvs.ipProto |> Modify] in
    let ipSrcAct = if minimize && act_hvs.ipSrc = match_hvs.ipSrc then [] else [SetIP4Src act_hvs.ipSrc |> Modify ] in
    let ipDstAct = if minimize && act_hvs.ipDst = match_hvs.ipDst then [] else [SetIP4Dst act_hvs.ipDst |> Modify ] in
    let tcpSrcAct = if minimize && act_hvs.tcpSrcPort = match_hvs.tcpSrcPort then [] else [SetTCPSrcPort act_hvs.tcpSrcPort |> Modify] in
    let tcpDstAct = if minimize && act_hvs.tcpDstPort = match_hvs.tcpDstPort then [] else [SetTCPDstPort act_hvs.tcpDstPort |> Modify] in
    let outPort = [Physical next_hop |> Output] in

    
    let act = List.concat [ethSrcAct; ethDstAct; vlanAct; vlanPcpAct; ethTypeAct;
                           ipProtoAct; ipSrcAct; ipDstAct; tcpSrcAct; tcpDstAct;
                           outPort] in
    
    { pattern      = match_pat;
      action       = [[act]];
      cookie       = 0L;
      idle_timeout = Permanent;
      hard_timeout = Permanent  }


  (*
   * Input is going to be 
   *  -- a policy (as netkat programs)
   *  -- the topology (as a netkat program) 
   *  -- the input packet 
   * Output needs to be
   *  -- the ingress switchID
   *  -- the OpenFlow rules to create special purpose packet
   *  -- the identifier of the end switch
   *  -- the OpenFlow rules to reinstate the special packet on the end switch
   *)
  let packet_tfx (policy:Syntax.policy) (pkt:packet) : ((switchId * OpenFlow.flow) * (switchId * OpenFlow.flow)) option =
    let open Option in
    let fdd_trace = fdd_trace_interp policy pkt in
    match fdd_trace with
    | [] -> failwith "NONE>>>>>" (*None Packet is dropped*)
    | (out_pkt, trace)::[] ->

       (match trace with 
        | [] -> None
        | first_hop :: loc_trace' ->
           let pt_trace' = List.map loc_trace' ~f:(fun l -> Syntax.getPhys l |> Int64.of_int32) in
           let src_route_packet = cannibalize_packet out_pkt pt_trace' in
           let traversed_packet = {src_route_packet
                                  with headers = {src_route_packet.headers
                                                 with ethDst = 0L}} in

           let first_hop_port = Syntax.getPhys first_hop in
           let ingress_tfx = flow_from_packet ~flow:pkt
                               ~action:src_route_packet
                               ~outport:first_hop_port
                               ~match_inport:true ~minimize:true
                               in
           
           (*Bind is in Option*)
           let egress_port = getPhys out_pkt.headers.location in
           let egress_tfx = flow_from_packet
                              ~flow:traversed_packet
                              ~action:out_pkt
                              ~outport:egress_port
                              ~match_inport:false
                              ~minimize:true in
           
           Some ((pkt.switch, ingress_tfx ),
                 (out_pkt.switch, egress_tfx))
       )
    | _::_ -> failwith "multicast is unsupported (for now)"
                       
      

end
(* END: module Automaton *)                
    
open Local_compiler
let compile ?(options=default_compiler_options) ?(pc=Field.Vlan) ?ing pol : FDD.t =
  prepare_compilation ~options pol;
  Automaton.of_policy pol
  |> Automaton.to_local ~pc


  
  
