open! Core

(** {2} timing function calls *)
let time f x =
  let t1 = Unix.gettimeofday () in
  let r = f x in
  let t2 = Unix.gettimeofday () in
  (t2 -. t1, r)

let timed descr f =
  printf "start %s...\n%!" descr;
  let t, y = time f () in
  printf "--> %s done! %f seconds\n%!" descr t;
  y

let print_time time =
  printf "time: %.4f\n" time


(** {2} mapping pairs  *)
let map_fst xs ~f =
  List.map xs ~f:(fun (x,y) -> (f x, y))

let map_snd xs ~f =
  List.map xs ~f:(fun (x,y) -> (x, f y))

let map_both xs ~f =
  List.map xs ~f:(fun (x,y) -> (f x, f y))



(** {2} useful higher order functions  *)
let tap x ~f =
  f x; x

let iter n ~f ~init =
  let rec loop n acc = if n <= 0 then acc else loop (n-1) (f acc) in
  loop n init



(*===========================================================================*)
(* open files with default application                                       *)
(*===========================================================================*)

type os =
  | MacOS
  | Linux

let detect_os () : os =
  let open Caml in
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  close_in ic;
  match uname with
  | "Darwin" -> MacOS
  | "Linux" -> Linux
  | _ -> failwith "unknown operating system"

let open_cmd =
  match detect_os () with
  | MacOS -> "open"
  | Linux -> "xdg-open"

let open_file f =
  let silence = "&> /dev/null" in
  Format.sprintf "%s %s % s" open_cmd f silence
  |> Caml.Unix.system
  |> ignore

(*===========================================================================*)
(* Graphviz                                                                  *)
(*===========================================================================*)

let compile_dot ?(format="pdf") ?(engine="dot") ?(title=engine) data : string =
  let output_file = Filename.temp_file (title ^ "_") ("." ^ format) in
  let to_dot = Unix.open_process_out (sprintf "dot -T%s -o %s" format output_file) in
  Out_channel.output_string to_dot data;
  Out_channel.close to_dot;
  ignore (Unix.close_process_out to_dot);
  output_file

let show_dot ?format ?title ?engine data : unit =
  compile_dot ?format ?title ?engine data
  |> open_file

let show_dot_file ?format ?title ?engine file : unit =
  In_channel.read_all file
  |> show_dot ?format ?title ?engine



(*===========================================================================*)
(* Logging                                                                   *)
(*===========================================================================*)

let with_logged_stdio ~log f =
  let module Unix = Caml.Unix in
  let stdout = Unix.dup Unix.stdout in
  let stderr = Unix.dup Unix.stderr in
  let log = Unix.descr_of_out_channel log in
  (* redirect stderr and stdout to log  *)
  Out_channel.(flush stdout); Unix.dup2 log Unix.stdout;
  Out_channel.(flush stderr); Unix.dup2 log Unix.stderr;
  protect ~f ~finally:(fun () ->
    (* restore stderr and stdout *)
    Unix.dup2 stdout Unix.stdout;
    Unix.dup2 stderr Unix.stderr;
  )

let green = "\027[32m"
let red = "\027[32m"
let no_color = "\027[0m"

let timed' descr ~log ~f =
  printf "%s%!" descr;
  match with_logged_stdio ~log (time f) with
  | exception e ->
    printf "\t%s[Err]%s\n%!" red no_color;
    raise e
  | (t,x) as result ->
    printf "\t%s[OK]%s\t(%.3f seconds)\n%!" green no_color t;
    result


