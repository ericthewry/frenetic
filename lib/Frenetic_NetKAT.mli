(** NetKAT Syntax

  The NetKAT language is central to Frenetic, and we factor out the central types here.  The big actors
  on NetKAT structures are Frenetic_NetKAT_Compiler which compiles NetKAT into flow tables,
  Frenetic_NetKAT_Parser which turns NetKAT strings (e.g "TcpSrcPort(8080); port := 2") into NetKAT, and
  Frenetic_NetKAT_Json which turns JSON-formatted NetKAT into NetKAT

*)

open Sexplib.Conv
open Core.Std
open Frenetic_Packet

(** {2 Basics} *)
(* thrown whenever local policy is expected, but global policy
  (i.e. policy containing links) is encountered *)
exception Non_local

type switchId = Frenetic_OpenFlow.switchId [@@deriving sexp, compare, eq]
type portId = Frenetic_OpenFlow.portId [@@deriving sexp, compare, eq]
type payload = Frenetic_OpenFlow.payload [@@deriving sexp]
type vswitchId = int64 [@@deriving sexp, compare, eq]
type vportId = int64 [@@deriving sexp, compare, eq]
type vfabricId = int64 [@@deriving sexp, compare, eq]

(** {2 Policies} *)

val string_of_fastfail : int32 list -> string

type location =
  | Physical of int32
  | FastFail of int32 list
  | Pipe of string
  | Query of string
  [@@deriving sexp, compare]

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
  [@@deriving sexp]

type pred =
  | True
  | False
  | Test of header_val
  | And of pred * pred
  | Or of pred * pred
  | Neg of pred
  [@@deriving sexp]

module Coin : sig
  type coin_label = int [@@deriving sexp]
  type coin_idx = int [@@deriving sexp]
  type prob = float
  type t [@@deriving sexp]
  (* type t = coin_label * coin_idx * prob [@@deriving sexp] *)
  module Set : Set.S with type Elt.t = t
  val compare : t -> t -> int
  val hash : t -> int
  val to_string : t -> string
  val prob : t -> float
  val mk_fresh : ?prob:float -> unit -> t
end

type policy =
  | Filter of pred
  | Mod of header_val
  | Union of policy * policy
  | Seq of policy * policy
  | Choice of policy * Coin.t * policy
  | Star of policy
  | Link of switchId * portId * switchId * portId
  | VLink of vswitchId * vportId * vswitchId * vportId
  [@@deriving sexp]

val id : policy
val drop : policy

(** {3 Applications} *)

type action = Frenetic_OpenFlow.action

type switch_port = switchId * portId [@@deriving sexp]
type host = Frenetic_Packet.dlAddr * Frenetic_Packet.nwAddr [@@deriving sexp]

type bufferId = Int32.t [@@deriving sexp] (* XXX(seliopou): different than Frenetic_OpenFlow *)

type event =
  | PacketIn of string * switchId * portId * payload * int
  | Query of string * int64 * int64
  | SwitchUp of switchId * portId list
  | SwitchDown of switchId
  | PortUp of switch_port
  | PortDown of switch_port
  | LinkUp of switch_port * switch_port
  | LinkDown of switch_port * switch_port
  | HostUp of switch_port * host
  | HostDown of switch_port * host
  [@@deriving sexp]
