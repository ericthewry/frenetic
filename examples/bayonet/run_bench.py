#!/usr/bin/env python3

from subprocess import call


def bayonet(k):
  return ['./run_bayonet.sh', 'bayonet_resilience_sw_%d.bayonet' % (4*k)]


def pnk(k, cps=True):
  if cps:
    return ['./run_probnetkat.sh', 'bayonet_resilience_sw_%d.dot' % (4*k)]
  else:
    return ['./run_probnetkat_no_cps.sh', 'bayonet_resilience_sw_%d.dot' % (4*k)]


def prism(k, approx=False):
  if approx:
    return ['./run_prism_approx.sh', str(k)]
  else:
    return ['./run_prism.sh', str(k)]


def run():
  run_bayonet = run_pnk = run_pnk_no_cps = run_prism = run_prism_approx = True
  for i in range(14):
    k = 2**i
    print("k = %d" % k)
    print("=" * 80)

    if run_bayonet:
      print("\nBAYONET")
      print("-" * 80)
      run_bayonet = call(bayonet(k)) == 0
    
    if run_pnk:
      print("\n\nPROBNETKAT")
      print("-" * 80)
      run_pnk = call(pnk(k, cps=True)) == 0

    if run_pnk_no_cps:
      print("\n\nPROBNETKAT (no CPS)")
      print("-" * 80)
      run_pnk_no_cps = call(pnk(k, cps=False)) == 0
    
    if run_prism:
      print("\n\nPRISM")
      print("-" * 80)
      run_prism = call(prism(k, approx=False)) == 0

    if run_prism_approx:
      print("\n\nPRISM (approximate)")
      print("-" * 80)
      run_prism_approx = call(prism(k, approx=True)) == 0
    
    print("\n\n")
  

if __name__ == "__main__":
  run()