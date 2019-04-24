open Core
module Netkat = Frenetic.Netkat
module Fdd = Netkat.Fdd.FDD
module Automaton = Netkat.Global_compiler.Automaton

(*===========================================================================*)
(* UTILITY FUNCTIONS                                                         *)
(*===========================================================================*)

let parse_topo (policyfile : string) = Netkat.Json.pol_of_topo_file policyfile
let parse_tables (policyfile :string) = Netkat.Json.pol_of_tables_file policyfile

let parse_pred file = Netkat.Parser.pred_of_file file

let fmt = Format.formatter_of_out_channel stdout
let _ = Format.pp_set_margin fmt 120

let print_fdd fdd =
  printf "%s\n" (Netkat.Local_compiler.to_string fdd)

let dump data ~file =
  Out_channel.write_all file ~data

let dump_rules paths ~file =
  dump ~file (Netkat.Json.paths_to_json_string paths)

open Frenetic.Async
module Controller = NetKAT_Controller.Make(OpenFlow0x01_Plugin)

let print_table fdd sw =
  Netkat.Local_compiler.to_table sw fdd
  |> Frenetic.OpenFlow.string_of_flowTable ~label:(sprintf "Switch %Ld" sw)
  |> printf "%s\n"

let time f =
  let t1 = Unix.gettimeofday () in
  let r = f () in
  let t2 = Unix.gettimeofday () in
  (t2 -. t1, r)

let print_time ?(prefix="") time =
  printf "%scompilation time: %.4f\n" prefix time


(*===========================================================================*)
(* COMMAND *)
(*===========================================================================*)

module Edge = struct
  let spec = Command.Spec.(
    empty
    +> anon ("topo" %: file)
    +> anon ("program" %: file)
  )

  let run topofile tablesfile () =
    let open Netkat.Global_compiler in
    let (edge, topo) = parse_topo topofile in
    let pol = parse_tables tablesfile in
    let program = Netkat.Syntax.(
        Seq(Seq(Seq(edge,pol),
                Star(Seq(topo, pol))
              ),
            edge)) in
    Printf.printf "%s\n\n" (Netkat.Pretty.string_of_policy program);
    let (t, rules) = time (fun () ->
                         Automaton.get_all_paths program ) in
    dump_rules rules ~file:("edge.json");
    print_time t;

end



(*===========================================================================*)
(* BASIC SPECIFICATION OF COMMANDS                                           *)
(*===========================================================================*)

let main : Command.t =
  Command.basic_spec
    ~summary:"Accepts topology file and table values, and compiles them to a source-routing scheme"
    (* ~readme: *)
    Edge.spec
    Edge.run 

