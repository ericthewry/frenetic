import argparse
import networkx as nx
import sys

from topologies import abfattree,fattree,jellyfish,vl2,xpander
from routing import allsp,spf,disjointtrees,routing_lib

DESTINATION = 's1'

def generate_topology(topo_args):
    targs = topo_args.split(',')
    topo = None
    # Fetch topology
    if targs[0] == 'fattree':
        pods = int(targs[1])
        topo = fattree.mk_topo(pods)
    elif targs[0] == 'abfattree':
        pods = int(targs[1])
        topo = abfattree.mk_topo(pods)
    elif targs[0] == 'vl2':
        da = int(targs[1])
        di = int(targs[2])
        topo = vl2.mk_topo(da, di, rack_size=1, bw='10Gbps')
    elif targs[0] == 'jellyfish':
        n = int(targs[1])
        k = int(targs[2])
        r = int(targs[3])
        topo = jellyfish.mk_topo(n, k, r)
    elif targs[0] == 'xpander':
        n = int(targs[1])
        k = int(targs[2])
        r = int(targs[3])
        topo = xpander.mk_topo(n, k, r)
    else:
        print "ERROR: Unknown topology."
    return topo

def routing_trees(topo, routing_alg, dest):
    trees = None
    if routing_alg == 'spf':
        trees = spf.route(topo, dest)
    elif routing_alg == 'allsp':
        trees = allsp.route(topo, dest)
    elif routing_alg == 'disjointtrees':
        trees = disjointtrees.route(topo, dest)
    else:
        print "ERROR: Unknown routing scheme."
    return trees

def network(topo_args, routing_algs, topo_name):
    if topo_name is None:
        topo_name = 'output/'+'_'.join(topo_args.split(','))
    # Generate topology
    topo = generate_topology(topo_args)
    if topo is None:
        print "ERROR: Failed to generate topology"
        return

    hosts = []
    num_switches = 0
    for n,d in topo.nodes(data=True):
        if d['type'] == 'host':
            hosts.append(n)
        elif d['type'] == 'switch':
            num_switches += 1

    # Export the topology
    nx.drawing.nx_agraph.write_dot(topo, topo_name + '_sw_' + str(num_switches) +'.dot')

    # Create a graph of only switches
    topo.remove_nodes_from(hosts)

    # Routing. Fix destination. Generate routing tree(s) to this desitnation
    alg_list = routing_algs.split(',')
    for alg in alg_list:
        routes = routing_trees(topo, alg, DESTINATION)
        routing_lib.serialize_routes(routes, topo_name+'-'+alg)


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-t','--topo',type=str,action='store',dest='topo_args',
                        default="fattree,4",
                        help='parameters for topology generation. e.g fattree,4')
    parser.add_argument('-r','--routing',type=str,action='store',dest='routing_algs',
                        default="spf,disjointtrees",
                        help='name of routing algorithms e.g spf')
    parser.add_argument('-o', '--out', action='store',dest='output',
                        default=None,
                        help='file name to write to')
    if len(sys.argv[4:]) == 0:
        parser.print_help()
        sys.exit()

    return parser.parse_args()

if __name__ == '__main__':
    args = parse_args()
    network(args.topo_args, args.routing_algs, args.output)