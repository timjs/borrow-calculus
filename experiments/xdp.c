#define ETH_P_IPV4 0x0800
SEC("xdp")
int xdp_prog(struct xdp_md *ctx) {
  void *data_end = (void *)(long)ctx->data_end;
  void *data = (void *)(long)ctx->data;
  struct ethhdr *eth = data;
  __u16 h_proto;
  if (data + sizeof(struct ethhdr) > data_end)
    return XDP_DROP;
  h_proto = eth->h_proto;
  for (int i = 0; i < h_proto; i++) {
    bpf_printk("%d", h_proto);
  }
  if (h_proto == htons(ETH_P_IPV4))
    return XDP_PASS;
  return XDP_DROP;
}
