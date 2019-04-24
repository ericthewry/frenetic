open Core
open Frenetic
open Netkat
open Semantics       
open Global_compiler


let load = Frenetic_kernel.OpenFlow.Buffered (0l, Cstruct.empty) 
let packet = { switch = 0L ;
               headers = HeadersValues.make ~ethDst:32L (); (* all zeros *)
               payload = load}



let show pkt =
  let port = match pkt.headers.location with
    | Physical x -> x
    | _ -> failwith "Borked"
  in
           
  "{ switch : " ^ Int64.to_string pkt.switch ^ ";\n"
  ^ "  port : " ^ Int32.to_string port ^  ";\n"
  ^ "  ethSrc : " ^ Int64.to_string pkt.headers.ethSrc ^ ";\n"
  ^ "  ethSrc : " ^ Int64.to_string pkt.headers.ethDst ^ ";\n"
  ^ "}"
                                               
       
let%test "Automaton produces expected packet" =
  (*
   * ((switch = 0; port = 0; ethSrc <- 2; port <- 1;
   * 0@1 => 1@0;
   * switch = 1; port = 0; ethSrc <- 5; port <- 1);
   *)
  let open Syntax in
  let polzero = Seq(Filter(Test(Switch 0L)),
                    Seq(Filter(Test(Location(Physical 0l))),
                        Seq(Mod (EthSrc 2L),
                            Mod (Location (Physical 1l))
                          )
                      )
                  ) in
  let polone = Seq(Filter(Test(Switch 1L)),
                    Seq(Filter(Test(Location(Physical 0l))),
                        Seq(Mod (EthSrc 5L),
                            Mod (Location (Physical 1l))
                          )
                      )
                 ) in
  let topo = Link(0L, 1l, 1L, 0l) in
  let prog = Seq(Seq(polzero, topo), polone) in
  let res = Automaton.fdd_trace_interp prog packet
            |> List.map ~f:fst in

  (* Printf.printf "[ ";
   * List.iter res ~f:(fun p -> Printf.printf "\n%s" (show p));
   * Printf.printf "]"; *)

  
  res = [{
            switch = 1L;
            headers = HeadersValues.make
                        ~location:(Physical 1l)
                        ~ethSrc:5L
                        ~ethDst:32L
                        ();
            payload = load
          }]

let%test "Packet is converted into matching flow" =
  let open OpenFlow in
  let in_pkt = { switch = 1L; headers = HeadersValues.make ~ethSrc:15L (); payload = load} in
  let out_pkt = {
      switch = 1L;
      headers = HeadersValues.make
                  ~location:(Physical 1l)
                  ~ethSrc:5L
                  ~ethDst:32L
                  ();
      payload = load
    } in
  let flow = {
      pattern = {
        dlSrc = Some 15L;
        dlDst = Some 0L;
        dlTyp = Some 0;
        dlVlan = Some 0;
        dlVlanPcp = Some 0;
        nwSrc = Some (0l, 32l);
        nwDst = Some (0l, 32l);
        nwProto = Some 0;
        tpSrc = Some 0;
        tpDst = Some 0;
        inPort = Some 0l;
      };
      action = [[[ Modify(SetEthSrc 5L);
                   Modify(SetEthDst 32L);
                   Modify(SetVlan(Some 0));
                   Modify(SetVlanPcp 0);
                   Modify(SetEthTyp 0);
                   Modify(SetIPProto 0);
                   Modify(SetIP4Src 0l);
                   Modify(SetIP4Dst 0l);
                   Modify(SetTCPSrcPort 0);
                   Modify(SetTCPDstPort 0);
                   Output(Physical 1l)                    
               ]]]
      ;
      cookie = 0L;
      idle_timeout = Permanent;
      hard_timeout = Permanent;
    } in
  flow = Automaton.flow_from_packet
           ~flow:in_pkt
           ~action:out_pkt
           ~outport:1l
           ~match_inport:true
           ~minimize:false

let%test "flow_from_packet Minimization only matches true modifications " =
  let open OpenFlow in
  let in_pkt = { switch = 1L;
                 headers = HeadersValues.make ();
                 payload = load} in
  let out_pkt = {
      switch = 9L;
      headers = HeadersValues.make
                  ~location:(Physical 1l)
                  ~ethSrc:5L
                  ~ethDst:32L
                  ~vlan:87
                  ~tcpSrcPort:32
                  ();
      payload = load
    } in
  
  [[[ Modify(SetEthSrc 5L);
      Modify(SetEthDst 32L);
      Modify(SetVlan(Some 87));
      Modify(SetTCPSrcPort 32);
      Output(Physical 1l)                    
  ]]] =
    (Automaton.flow_from_packet
       ~flow:in_pkt
       ~action:out_pkt
       ~outport:1l
       ~match_inport:true
       ~minimize:true).action

let%test "flow_from_packet DONT_CARE's on the inport when given the appropriate flag " =
  let open OpenFlow in
  let in_pkt = { switch = 1L; headers = HeadersValues.make (); payload = load} in
  let out_pkt = {switch = 9L; headers = HeadersValues.make (); payload = load} in
  let flow = Automaton.flow_from_packet
               ~flow:in_pkt
               ~action:out_pkt
               ~outport:1l
               ~match_inport:false
               ~minimize:true
  in
  Option.is_none flow.pattern.inPort
  
let packets_equal_except_ethDst pkt pkt' =
  pkt.switch = pkt'.switch
  && pkt.payload = pkt'.payload
  && pkt.headers.location = pkt'.headers.location
  && pkt.headers.from = pkt'.headers.from
  && pkt.headers.abstractLoc = pkt'.headers.abstractLoc
  && pkt.headers.ethSrc = pkt'.headers.ethSrc
  && pkt.headers.vlan = pkt'.headers.vlan
  && pkt.headers.vlanPcp = pkt'.headers.vlanPcp
  && pkt.headers.vswitch = pkt'.headers.vswitch
  && pkt.headers.vport = pkt'.headers.vport
  && pkt.headers.ethType = pkt'.headers.ethType
  && pkt.headers.ipProto = pkt'.headers.ipProto
  && pkt.headers.ipSrc = pkt'.headers.ipSrc
  && pkt.headers.ipDst = pkt'.headers.ipDst
  && pkt.headers.tcpSrcPort = pkt'.headers.tcpDstPort                                                     

let%test "cannibalize_packet overwrites dstMac correctly [Empty Trace]" =
  let pkt = {switch = 0L;
             headers = HeadersValues.make ~ethDst:40L ();
             payload = load} in
  let trace = [] in
  let c_pkt = Automaton.cannibalize_packet pkt trace in
  (* Packets are mostly the same *)
  packets_equal_except_ethDst pkt c_pkt
  (*Except for the dstMac which has been zeroed out*)     
  && c_pkt.headers.ethDst = 0L
  && pkt.headers.ethDst = 40L

let%test "cannibalize_packet overwrites dstMac correctly [NonEmpty Trace]" =
  let pkt = {switch = 0L;
             headers = HeadersValues.make ~ethDst:40L ();
             payload = load} in
  let trace = [5L; 30L; 19L; 6L; 1L] in
  let trace_enc = "0b"
                  ^ "100101" (* 5 *)
                  ^ "111110" (*30*)
                  ^ "110011" (*19*)
                  ^ "100110" (*6*)
                  ^ "100001" (*1*)
                  ^ "000000" (* _ *)
                  ^ "000000" (* _ *)
                  ^ "000000" (* _ *) in
  let c_pkt = Automaton.cannibalize_packet pkt trace in
  (* Packets are mostly the same *)
  packets_equal_except_ethDst pkt c_pkt
  (*Except for the dstMac which represents the bitstring*)
  && c_pkt.headers.ethDst = Int64.of_string trace_enc
  && pkt.headers.ethDst = 40L


                            
                                
                                                     
let%test "Automaton refines PacketSet" =
  let in_pkt = {switch = 0L;
                headers = HeadersValues.make ();
                payload = load} in
  let pol = Syntax.(
      List.fold ~init:Syntax.id ~f:(fun acc s -> Seq(acc, s))
        [Filter (And(Test(Switch 0L),
                     Test(Location(Physical 0l))));
         Mod(Vlan 20);
         Mod(EthDst 10L);
         Mod(EthSrc 100L);
         Mod(Location(Physical 1l));
         
         Link(0L, 1l, 1L, 0l);
         Filter(And(Test(Switch 1L),
                    Test(Location(Physical 0l))));
         Mod(Vlan 5);
         Mod(EthSrc 47L);
         Mod(Location(Physical 1l));
         
         Link(1L, 1l, 3L, 0l);
         Filter(And(Test(Switch 3L),
                    Test(Location(Physical 0l))));
         Mod(Vlan 0);
         Mod(EthSrc 5L);
         Mod(EthDst 20L);
         Mod(Location(Physical 1l))
        ])
  in
  let sem = Semantics.eval in_pkt pol in
  Automaton.fdd_trace_interp pol in_pkt
  |> fun l ->
     List.fold l
       ~init:(List.length l >= PacketSet.length sem)
       ~f:(fun c (p,_) -> c && PacketSet.mem sem p)

let%test "Packet is correctly translated in automaton " =
  let open OpenFlow in
  (* Printf.printf "-------------------------------------------\n";
   * Printf.printf "PACKET IS CORRECTLY TRANSLATED IN AUTOMATON\n";
   * Printf.printf "-------------------------------------------\n"; *)

  let in_pkt = {switch = 0L;
                headers = HeadersValues.make ();
                payload = load} in
  let pol = Syntax.(
      List.fold ~init:Syntax.id ~f:(fun acc s -> Seq(acc, s))
        [Filter (And(Test(Switch 0L),
                     Test(Location(Physical 0l))));
         Mod(Vlan 20);
         Mod(EthDst 10L);
         Mod(EthSrc 100L);
         Mod(Location(Physical 1l));
         
         Link(0L, 1l, 1L, 0l);
         Filter(And(Test(Switch 1L),
                    Test(Location(Physical 0l))));
         Mod(Vlan 5);
         Mod(EthSrc 47L);
         Mod(Location(Physical 1l));
         
         Link(1L, 1l, 3L, 0l);
         Filter(And(Test(Switch 3L),
                    Test(Location(Physical 0l))));
         Mod(Vlan 0);
         Mod(EthSrc 5L);
         Mod(EthDst 20L);
         Mod(Location(Physical 1l))
        ])
  in
  let trace = Int64.of_string
                ("0b"
                 ^ "100001"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                )  in (*TRACE*)
  let out_pkt = {switch = 0L;
                 headers = HeadersValues.make
                             ~ethSrc:5L
                             ~ethDst:20L                             
                             ();
                 payload = load }  in
  
  (match Automaton.packet_tfx pol in_pkt with
  | None -> failwith "Error, should not be None"
  | Some ((i, fi),(o, fo)) ->
     (* let fmt = Format.str_formatter in
      * format_group fmt fi.action;
      * Printf.printf "in_actions -\n%s\n" (Format.flush_str_formatter ());
      * Printf. printf "Expected -\n EthSrc(%s) EthDst(%s) Output(1)\n"
      *           (Int64.to_string out_pkt.headers.ethSrc)
      *           (Int64.to_string trace);
      * Printf.printf "/----------------------------------------------\n";
      * Printf.printf "end packet is correctly translated in automaton\n";
      * Printf.printf "/----------------------------------------------\n"; *)

     
     let ingress_actions = List.nth_exn (List.nth_exn fi.action 0) 0 in

     fi.pattern.dlSrc = Some in_pkt.headers.ethSrc
     && fi.pattern.dlDst = Some in_pkt.headers.ethDst
     && fi.pattern.dlTyp = Some in_pkt.headers.ethType
     && fi.pattern.dlVlan = Some in_pkt.headers.vlan
     && fi.pattern.dlVlanPcp = Some in_pkt.headers.vlanPcp
     && fi.pattern.nwSrc = Some (in_pkt.headers.ipSrc, 32l)
     && fi.pattern.nwDst = Some (in_pkt.headers.ipDst, 32l)
     && fi.pattern.nwProto = Some in_pkt.headers.ipProto
     && fi.pattern.tpSrc = Some in_pkt.headers.tcpSrcPort
     && fi.pattern.tpDst = Some in_pkt.headers.tcpDstPort
     && fi.pattern.inPort = Some (Syntax.getPhys in_pkt.headers.location)

     && List.nth ingress_actions 0 = Some(Modify(SetEthSrc out_pkt.headers.ethSrc))


     && fi.action = [[[
                         Modify(SetEthSrc out_pkt.headers.ethSrc);
                         Modify(SetEthDst trace);
                         Output(Physical 1l)
                    ]]]
     
     
     
     && fo.pattern.dlSrc = Some out_pkt.headers.ethSrc
     && fo.pattern.dlDst = Some 0L
     && fo.pattern.dlTyp = Some out_pkt.headers.ethType
     && fo.pattern.dlVlan = Some out_pkt.headers.vlan
     && fo.pattern.dlVlanPcp = Some out_pkt.headers.vlanPcp
     && fo.pattern.nwSrc = Some (out_pkt.headers.ipSrc, 32l)
     && fo.pattern.nwDst = Some (out_pkt.headers.ipDst, 32l)
     && fo.pattern.nwProto = Some out_pkt.headers.ipProto
     && fo.pattern.tpSrc = Some out_pkt.headers.tcpSrcPort
     && fo.pattern.tpDst = Some out_pkt.headers.tcpDstPort
     && fo.pattern.inPort = None

     && fo.action = [[[ Modify(SetEthDst out_pkt.headers.ethDst);
                        Output(Physical 1l)
                    ]]]
  )
                      


module BarbellTopo = struct
  open OpenFlow
  open Syntax
  (*
      
     0--[1]--4------------2[2]3---------9[3]7-------------0[47]---2
         \2                /1             \3                /12
          \----3[4]2------/                \---9[10]27-----/
  
   *)
  
  let topo =
    List.fold ~init:drop ~f:(fun acc (sw, pt, sw', pt') ->
        Union(acc, Union(Link( sw,  pt, sw', pt'),
                         Link(sw', pt',  sw, pt))))                                   
    [(1L, 4l, 2L, 2l);
     (1L, 2l, 4L, 3l);
     (4L, 2l, 2L, 1l);
     (2L, 3l, 3L, 9l);
     (3L, 3l, 10L, 9l);
     (3L, 7l, 47L, 0l);
     (10L, 27l, 47L, 12l)]


  (*Policy : 
      1 & 47 are edge-nodes
      Send Packets destined for 0.0.0.1 to 47@2 
      -- take path 1, 4, 2, 3, 47
      Send Packets destined for 0.0.0.2 to 1@0
      -- take path 47, 10, 3, 2, 1
   *)

  let flow1 = Seq(Filter(And(Test (Switch 1L), Test (Location (Physical 1l)))),
                  
                  Union(Seq(Filter(Test(IP4Dst (2l,32l))), Mod(Location (Physical 0l))),
                        Seq(Seq(Filter(Test(IP4Dst (1l,32l))),
                                Mod(Location (Physical 2l))),
                            Seq(Link(1L,2l,3L,4l),
                            Seq(Mod(Location(Physical 2l)),
                            Seq(Link(3L,2l,2L,1l),
                            Seq(Mod(Location(Physical 3l)),
                            Seq(Link(2L,3l, 3L, 9l),
                            Seq(Mod(Location(Physical 7l)),
                            Seq(Link(3L,7l, 47L, 0l),
                                Mod(Location(Physical 2l))))))))))))
                 
  let flow2 = Seq(Filter(And(Test (Switch 47L), Test (Location (Physical 2l)))),
                  Union(Seq(Filter(Test(IP4Dst (1l,32l))), Mod(Location (Physical 2l))),
                        Seq(Seq(Filter(Test(IP4Dst (2l,32l))),
                                Mod(Location (Physical 12l))),
                        Seq(Link(47L,12l,10L,27l),
                        Seq(Mod(Location(Physical 9l)),
                        Seq(Link(10L,9l,3L,3l),
                        Seq(Mod(Location(Physical 9l)),
                        Seq(Link(3L,9l,2L,3l),
                        Seq(Mod(Location(Physical 2l)),
                        Seq(Link(2L,2l,1L,4l),
                            Mod(Location(Physical 0l))))))))))))

  let test_packet ~ingress:in_pkt ~egress:out_pkt ~trace:trace ~iport:iport ~eport:eport =
    let prog' = Union(flow1, flow2) in
    match Automaton.packet_tfx prog' in_pkt with
    | None -> failwith "Error, should not be None"
    | Some ((i, fi),(o, fo)) ->

       (* let fmt = Format.str_formatter in
        * format_group fmt fo.action;
        * Printf.printf "out_actions -\n%s\n" (Format.flush_str_formatter ());
        * Printf.printf "EthDst <- %s\n" (Int64.to_string out_pkt.headers.ethDst);
        * Printf.printf "port <- %s\n\n" (Int32.to_string eport); *)

     
       let ingress_actions = List.nth_exn (List.nth_exn fi.action 0) 0 in
       fi.pattern.dlSrc = Some in_pkt.headers.ethSrc
       && fi.pattern.dlDst = Some in_pkt.headers.ethDst
       && fi.pattern.dlTyp = Some in_pkt.headers.ethType
       && fi.pattern.dlVlan = Some in_pkt.headers.vlan
       && fi.pattern.dlVlanPcp = Some in_pkt.headers.vlanPcp
       && fi.pattern.nwSrc = Some (in_pkt.headers.ipSrc, 32l)
       && fi.pattern.nwDst = Some (in_pkt.headers.ipDst, 32l)
       && fi.pattern.nwProto = Some in_pkt.headers.ipProto
       && fi.pattern.tpSrc = Some in_pkt.headers.tcpSrcPort
       && fi.pattern.tpDst = Some in_pkt.headers.tcpDstPort
       && fi.pattern.inPort = Some (Syntax.getPhys in_pkt.headers.location)
                                           
       && fi.action = [[[
                           Modify(SetEthDst trace);
                           Output(Physical iport)
                      ]]]
                        
                        
                        
       && fo.pattern.dlSrc = Some out_pkt.headers.ethSrc
       && fo.pattern.dlDst = Some 0L
       && fo.pattern.dlTyp = Some out_pkt.headers.ethType
       && fo.pattern.dlVlan = Some out_pkt.headers.vlan
       && fo.pattern.dlVlanPcp = Some out_pkt.headers.vlanPcp
       && fo.pattern.nwSrc = Some (out_pkt.headers.ipSrc, 32l)
       && fo.pattern.nwDst = Some (out_pkt.headers.ipDst, 32l)
       && fo.pattern.nwProto = Some out_pkt.headers.ipProto
       && fo.pattern.tpSrc = Some out_pkt.headers.tcpSrcPort
       && fo.pattern.tpDst = Some out_pkt.headers.tcpDstPort
       && fo.pattern.inPort = None
       
       && fo.action = [[[ Modify(SetEthDst out_pkt.headers.ethDst);
                          Output(Physical eport)
                      ]]]
end
                      
let%test "Barbell Example" =
  let open BarbellTopo in

  (* Printf.printf "-------------------------------------------\n";
   * Printf.printf "              Barbell\n";
   * Printf.printf "-------------------------------------------\n"; *)

  
  let in_pkt1 = { switch = 1L;
                  headers = HeadersValues.make
                              ~ethDst:100L
                              ~location:(Physical 1l)
                              ~ipDst:1l ();
                 payload = load} in
  
  let trace1 = Int64.of_string
                ("0b100010" (* 2 *)
                 ^ "100011" (* 3 *)
                 ^ "100111" (* 7 *)
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                 ^ "000000"
                )  in
  let out_pkt1 = {switch = 47L;
                 headers = HeadersValues.make ~ipDst:1l ~ethDst:100L ();
                 payload = load }  in

  let in_pkt2 = { switch = 47L;
                  headers = HeadersValues.make
                              ~ethDst:200L
                              ~ipDst:2l
                              ~location:(Physical 2l)
                              ();
                  payload = load} in
  let trace2 = Int64.of_string
                 ("0b101001" (* 9 *)
                  ^ "101001" (* 9 *)
                  ^ "100010" (* 2 *)
                  ^ "000000" 
                  ^ "000000"
                  ^ "000000"
                  ^ "000000"
                  ^ "000000"
                 )  in
  let out_pkt2 = { switch = 1L;
                   headers = HeadersValues.make ~ipDst:2l ~ethDst:200L ();
                   payload = load} in
  

  test_packet ~ingress:in_pkt1 ~egress:out_pkt1 ~trace:trace1 ~iport:2l ~eport:2l &&
    test_packet ~ingress:in_pkt2 ~egress:out_pkt2 ~trace:trace2 ~iport:12l ~eport:0l
