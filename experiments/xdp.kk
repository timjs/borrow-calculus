val eth-p-ipv4 = 0x0800

@section("xdp")
fun xdp-prog(ctx: xdp/md) -> i32
  match ctx.data       // Safe unpacking of data
    None -> xdp/Drop   // Implicit return
    Some(eth) ->       // Immutable variables by default
      val h-proto = eth.h-proto  // Type inference
      h-proto.times() {  // Bounded loops only
        bpf/print(h_proto)
      }
      if h-proto == htons(eth-p-ipv4)
        then xdp/Pass
        else xdp/Drop
