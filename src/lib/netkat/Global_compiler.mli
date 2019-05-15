open Syntax
open Core
       
module OpenFlow : module type of Frenetic_kernel.OpenFlow
module Util : module type of Frenetic_kernel.Util
module FDD : module type of Local_compiler.FDD
module Interp : module type of Local_compiler.Interp
                              
(** Intermediate representation of global compiler: NetKAT Automata *)
module Automaton : sig
  type t = private
    { states : (int64, FDD.t * FDD.t) Hashtbl.t;
      has_state : (FDD.t * FDD.t, int64) Hashtbl.t;
      mutable source : int64;
      mutable nextState : int64 }

  val add_to_t : t -> (FDD.t * FDD.t) -> int64

  val fold_reachable: ?order:[< `Post | `Pre > `Pre ]
    -> t
    -> init:'a
    -> f:('a -> int64 -> (FDD.t * FDD.t) -> 'a)
    -> 'a

  val of_policy: ?dedup:bool -> ?ing:pred -> ?cheap_minimize:bool -> policy -> t
  val to_local: pc:Fdd.Field.t -> t -> FDD.t

  val to_dot: t -> string

  val render : ?format:string -> ?title:string -> t -> unit
  (** Compiles the provided automaton `t` using `graphviz`, and opens the resulting
      file. *)

  (* open Semantics                                                         
   * val fdd_trace_interp : policy -> packet -> (packet * (Syntax.location list)) list
   * (\* val cannibalize_packet : packet -> int64 list -> packet *\)
   * (\* val flow_from_packet : flow:packet -> action:packet -> outport:OpenFlow.portId ->
   *  *                        match_inport:bool -> minimize:bool  -> OpenFlow.flow *\)
   * (\* val packet_tfx : policy -> packet -> ((switchId * OpenFlow.flow) * (switchId * OpenFlow.flow)) option *\) *)

  val get_all_paths : ?render_auto:bool ->
                      policy -> ((((bool * (Fdd.Field.t * Fdd.Value.t)) list) option)
                                 * (int64 list)
                                 * (Fdd.Field.t * Fdd.Value.t) list
                                ) list

  val path_match : ?render_auto:bool -> policy -> policy ->
                   ((bool * (Fdd.Field.t * Fdd.Value.t)) list * (Fdd.Field.t * Fdd.Value.t) list *
                      (bool * (Fdd.Field.t * Fdd.Value.t)) list * (Fdd.Field.t * Fdd.Value.t) list)
                     list
                         
  val skip_topo_states : t
    -> ((int64, (int64 * int64)) Hashtbl.t * ((int64 * int64), Int64.Set.t) Hashtbl.t)

end
                     
val compile : ?options:Local_compiler.compiler_options
           -> ?pc:Fdd.Field.t
           -> ?ing:pred
           -> policy
           -> FDD.t
(** [compile p] compiles the policy [p] into an FDD. The pc field is used for
    internal bookkeeping and must *not* be accessed or written to by the input
    policy [p].
*)
