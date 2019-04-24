open Sexplib.Conv
open Core

open Frenetic_kernel.Packet

exception Non_local

type switchId = Frenetic_kernel.OpenFlow.switchId [@@deriving sexp, compare, eq]
type portId = Frenetic_kernel.OpenFlow.portId [@@deriving sexp, compare, eq]
type payload = Frenetic_kernel.OpenFlow.payload [@@deriving sexp]
type vswitchId = int64 [@@deriving sexp, compare, eq]
type vportId = int64 [@@deriving sexp, compare, eq]
type vfabricId = int64 [@@deriving sexp, compare, eq]
type metaId = string [@@deriving sexp, compare, eq]
type abstract_location = string [@@deriving sexp, compare, eq, hash]

let string_of_fastfail = Frenetic_kernel.OpenFlow.format_list ~to_string:Int32.to_string

type location =
  | Physical of int32
  | FastFail of int32 list
  | Pipe of string
  | Query of string
  [@@deriving sexp, compare]

let getPhys loc =
  match loc with
  | Physical i -> i
  | FastFail _ -> failwith "Cannot get Physical Location from FastFail"
  | Pipe _ -> failwith "Cannot get Physical Location from Pipe"
  | Query _ -> failwith "Cannot get Physical Location from Query "
  
type header_val =
  | Switch of switchId
  | Location of location
  | EthSrc of dlAddr
  | EthDst of dlAddr
  | Vlan of int16
  | VlanPcp of dlVlanPcp
  | EthType of dlTyp
  | IPProto of nwProto
  | IP4Src of nwAddr * int32
  | IP4Dst of nwAddr * int32
  | TCPSrcPort of tpPort
  | TCPDstPort of tpPort
  | VSwitch of vswitchId
  | VPort of vportId
  | VFabric of vfabricId
  | Meta of metaId * int64
  | From of abstract_location
  | AbstractLoc of abstract_location
                     [@@deriving sexp]

let string_of_header_val j hv =
  match hv with
  | Switch swid -> "switch" ^ j ^ Int64.to_string swid
  | Location (Physical p) -> "port" ^ j ^ Int32.to_string p
  | EthSrc e -> "ethSrc" ^ j ^ Int64.to_string e
  | EthDst e -> "ethDst" ^ j ^ Int64.to_string e
  | Vlan v -> "vlan" ^ j ^ Int.to_string v
  | VlanPcp p -> "vlanPCP"  ^ j ^ Int.to_string p
  | EthType t -> "ethType" ^ j ^ Int.to_string t
  | IP4Src (i,m) -> "ip4Src" ^ j ^ Int32.to_string i ^ "/" ^ Int32.to_string m
  | IP4Dst (i,m) -> "ip4Dst" ^ j ^ Int32.to_string i ^ "/" ^ Int32.to_string m
  | TCPSrcPort t -> "tcpSrcPort" ^ j ^ Int.to_string t
  | TCPDstPort t -> "tcpSrcPort" ^ j ^ Int.to_string t
  | _ -> failwith "Dont know how to stringify that"

type pred =
  | True
  | False
  | Test of header_val
  | And of pred * pred
  | Or of pred * pred
  | Neg of pred
  [@@deriving sexp]

let rec string_of_pred p =
  match p with
  | True -> "True"
  | False -> "False"
  | Test hv -> string_of_header_val " = " hv
  | And (p',p'') -> string_of_pred p' ^ "; " ^ string_of_pred p''
  | Or (p', p'') -> string_of_pred p' ^ "+ " ^ string_of_pred p''
  | Neg p' -> "~" ^ string_of_pred p' 
              

type meta_init =
  | Alias of header_val
  | Const of int64
  [@@deriving sexp]

type policy =
  | Filter of pred
  | Mod of header_val
  | Union of policy * policy
  | Seq of policy * policy
  | Star of policy
  | Link of switchId * portId * switchId * portId
  | VLink of vswitchId * vportId * vswitchId * vportId
  | Let of { id : metaId; init : meta_init; mut : bool; body : policy }
  | Dup
  [@@deriving sexp]

let rec string_of_policy p =
  match p with
  | Filter t -> "filter (" ^ string_of_pred t ^ ")"
  | Mod hv -> string_of_header_val " := " hv
  | Union (p',p'')  -> "(" ^ string_of_policy p' ^  ") + (" ^ string_of_policy p'' ^ ")"
  | Seq (p', p'') -> string_of_policy p' ^ "; " ^ string_of_policy p''
  | Star p' -> "(" ^ string_of_policy p' ^ ")* "
  | Link (sw, pt, sw', pt') -> let atstring x y = Int64.to_string x ^ "@" ^ Int32.to_string y in
                               atstring sw pt ^ "=>" ^ atstring sw' pt'
  | VLink (_,_,_,_) -> failwith "do not know how to print VLink"
  | Let _ -> failwith "do not know how to print Let"
  | Dup -> "dup"
  
let id = Filter True
let drop = Filter False

type action = Frenetic_kernel.OpenFlow.action

type switch_port = switchId * portId [@@deriving sexp]
type host = Frenetic_kernel.Packet.dlAddr * Frenetic_kernel.Packet.nwAddr [@@deriving sexp]

type bufferId = Int32.t [@@deriving sexp] (* XXX(seliopou): different than OpenFlow *)

