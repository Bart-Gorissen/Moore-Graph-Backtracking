import sys
import itertools
import more_itertools
import networkx as nx
import time
import math
import matplotlib.pyplot as plt
import os
import json

######################################
# GLOBAL VARIABLES
######################################

# graph properties
n = 3250     # nodes in Moore(k, d) (=k*k + 1)
k = 57       # node degree
d = 2        # graph diameter
g = 5        # graph girth (=2d+1)

# file storage
name = "tmp" # identifier for storing results

# counters
cnt = 0      # number of k-regular graphs seen
g_cnt = 0    # number of graphs seen



######################################
# AUXILIARY FUNCTIONS
######################################

def find_min_len_cycle(G, v):
    """
    Finds a minimum length cycle involving v, stops early when minimum cycle of length less than g has been found
    :param G: Graph
    :param v: node v on which to find a cycle
    :return: minimum length cycle involving v, or the length of a cycle involving v less than g
    """
    global g

    min_len = n+1
    toVisit = [ (v, 0, [v]) ]

    while len(toVisit) > 0:
        (u, dist, p_cycle) = toVisit[0]
        toVisit.pop(0)

        # if there exists an edge from u to v
        # where u is at distance at least 2 from v (in the search tree)
        # then have a cycle
        if dist >= 2 and G.has_edge(u, v):
            if  dist+1 < min_len:
                min_len = dist+1
                # we violate the girth, so return
                if min_len < g:
                    return min_len
            continue

        toVisit.extend([ (w, dist+1, p_cycle+[u]) for w in G.neighbors(u) if w not in p_cycle ])

    return min_len

def has_girth_g(G):
    """
    Check whether graph has girth g
    :param G: Graph
    :return: girth(G) == g
    """
    global n, g

    ub_girth = n+1

    for i in range(n):
        g_i = find_min_len_cycle(G, i)
        if g_i < g:
            return False
        if g_i < ub_girth:
            ub_girth = g_i

    if ub_girth == g:
        return True

    return False

def update_degrees(lst, i, adj):
    """
    Given a list of node degrees of a graph, vertex i, and new neighbours of i, update degree list
    :param lst: degree list
    :param i: index from which to add neighbours
    :param adj: newly added neighbours of i
    :return: updated list of degrees
    """
    lst[i] += len(adj)
    for e in adj:
        lst[e] += 1
    return lst

def revert_degrees(lst, i, adj):
    """
    Given a list of node degrees of a graph, vertex i, and new neighbours of i, revert degree list
    :param lst: degree list
    :param i: index from which to add neighbours
    :param adj: newly added neighbours of i
    :return: reverted list of degrees
    """
    lst[i] -= len(adj)
    for e in adj:
        lst[e] -= 1
    return lst

def valid_degrees(lst):
    """
    Checks whether none of the entries exceed k
    :param lst: list of integers
    :return: forall l in lst: l <= k
    """
    global k
    for deg in lst:
        if deg > k:
            return False

    return True

def full_degrees(lst):
    """
    Checks whether all entries are exactly k
    :param lst: list of integers
    :return: forall l in lst: l == k
    """
    global k
    for deg in lst:
        if deg != k:
            return False

    return True

def check_validity(G):
    """
    Checks whether a k-regular graph is a valid Moore Graph
    :param G: graph
    :return: G == Moore(k, d)
    """
    global n, d, g

    if not nx.is_connected(G):
        return False

    # check that diameter = d, and girth is 2d+1
    if nx.diameter(G) != d:
        return False

    if not has_girth_g(G):
        return False

    return True



######################################
# BACKTRACKING
######################################

def recursive_pre():
    """
    Initialization for backtracking routine
    :return: result from backtracking
    """
    deg = [0 for i in range(n)]
    G = nx.empty_graph(n)

    return recursive(G, 0, deg)

def recursive(G, i, deg):
    """
    Backtracking routine for finding a Moore graph Moore(k, d)
    :param G: graph
    :param i: node until which graph construction is complete (not-including)
    :param deg: list of node degrees corresponding to G
    :return: exists G' modification of G : G == Moore(k, d) -> (True, G). Otherwise (False, 0)
    """
    global n, k, cnt
    # i : which vertex should be set next

    # if we are done
    if i == n-1:
        cnt += 1
        if cnt % 1000 == 0:
            print("Processed", cnt, "graphs")

        if not full_degrees(deg): # graph should be k-regular
            return False, 0

        if not check_validity(G): # graph should be Moore graph
            return False, 0

        return True, G

    # if node i already has degree k, then no edges are added
    if deg[i] == k:
        return recursive(G, i+1, deg)

    # we specify k-deg[i] edges from i to nodes after i, and recurse on all (seeminly valid) options
    for adj in itertools.combinations(range(i + 1, n), k - deg[i]):
        update_degrees(deg, i, adj)
        if not valid_degrees(deg):
            revert_degrees(deg, i, adj)
            continue

        # edges specified by adj
        edges = [(i, j) for j in adj]
        G.add_edges_from(edges)

        res, G_out = recursive(G, i+1, deg)
        if res:
            return res, G_out

        # revert degree list and graph for next option
        G.remove_edges_from(edges)
        revert_degrees(deg, i, adj)

        # the neighbours for node 0 can be chosen arbitrarily
        if i == 0:
            break;

    return False, 0



######################################
# ITERATIVE
######################################

def next_valid(G, deg, enc, edges_from, next_con):
    """
    Given a graph encoding, construct the next valid k-regular graph
    :param G: graph
    :param deg: degree list corresponding to the graph
    :param enc: encoding (for each node i, contains the index of adjacency generator to use)
    :param edges_from: how many edges are constructed from each node
    :param next_con: the next node to be considered in graph construction
    :return: next (by encoding) k-regular graph, degree list, encoding, and edge counts per node
    """
    global n, k, name, g_cnt

    while next_con < n and enc[0] == 0:
        # has already got degree k
        if k == deg[next_con]:
            edges_from[next_con] = 0
            next_con += 1
            continue

        max_comb = math.comb(n-1-next_con, k-deg[next_con])

        while enc[next_con] < max_comb:
            adj = more_itertools.nth_combination(range(next_con + 1, n), k-deg[next_con], enc[next_con])
            update_degrees(deg, next_con, adj)
            if valid_degrees(deg):
                break

            revert_degrees(deg, next_con, adj)
            enc[next_con] += 1

        # if no k-regular valid found, go to previous
        if enc[next_con] == max_comb:
            enc[next_con] = 0
            next_con -= 1

            while edges_from[next_con] == 0:
                next_con -= 1

            # remove previous choice different counter
            adj = more_itertools.nth_combination(range(next_con + 1, n), edges_from[next_con], enc[next_con])
            edges = [(next_con, j) for j in adj]
            G.remove_edges_from(edges)
            revert_degrees(deg, next_con, adj)

            # update encoding counter
            enc[next_con] += 1
            continue

        # otherwise, have a valid encoding, add to graph
        edges = [(next_con, j) for j in adj]
        G.add_edges_from(edges)
        edges_from[next_con] = len(edges)
        next_con += 1

        # store encoding if needed
        g_cnt += 1
        if g_cnt % 100000 == 0:
            print("Saving encoding", g_cnt)
            with open("out/enc"+name+".json", "w+") as fj:
                json.dump(enc, fj)

    return G, deg, enc, edges_from

def iterative(quick):
    """
    Iterative routine for finding a Moore graph Moore(k, d)
    :param quick: whether to use last stored encoding
    :return: exists G' modification of G : G == Moore(k, d) -> (True, G). Otherwise (False, 0)
    """
    global n, k, cnt, name

    G = nx.empty_graph(n)
    deg = [0 for i in range(n)]
    enc = [0 for i in range(n)]
    edges_from = [0 for i in range(n)]

    if quick and os.path.exists("out/enc"+name+".json"):
        print("Loading encoding")
        with open("out/enc"+name+".json", "r") as fj:
            enc = json.load(fj)
    else:
        print("Starting from scratch")

    # find next valid graph
    print("Constructing initial graph...")
    G, deg, enc, edges_from = next_valid(G, deg, enc, edges_from, 0)

    if enc[0] != 0:
        print("No such k-regular graph exists")
        return False, 0

    print("Constructed initial graph")

    res, G_res = False, 0

    # check if initial graph is solution
    if full_degrees(deg):
        if check_validity(G):
            res = True
            G_res = G
    cnt += 1

    # if not, remove last added set of edges and get next graph (choice of edges from node 0 is not relevant)
    while not res and enc[0] == 0:
        next_con = n-1
        while edges_from[next_con] == 0:
            next_con -= 1

        adj = more_itertools.nth_combination(range(next_con + 1, n), edges_from[next_con], enc[next_con])
        edges = [(next_con, j) for j in adj]
        G.remove_edges_from(edges)
        revert_degrees(deg, next_con, adj)

        # update encoding counter
        enc[next_con] += 1

        G, deg, enc, edges_from = next_valid(G, deg, enc, edges_from, next_con)

        if full_degrees(deg):
            if check_validity(G):
                res = True
                G_res = G
        cnt += 1
        if cnt % 1000 == 0:
            print("Processed", cnt, "graphs")

    # store encoding of solution if found
    if res:
        with open("out/solution_enc"+name+".json", "w+") as fj:
            json.dump(enc, fj)

    return res, G_res



######################################
# MAIN METHODS
######################################

def do_backtrack(method, stored):
    global n, k, d, g, name

    name = str(k)+"_"+str(d)

    t_start = time.time()
    if method == "recursive":
        print("Starting recursive method")
        res, G_res = recursive_pre()
    elif method == "iterative":
        print("Starting iterative method")
        res, G_res = iterative(stored)
    print("Time taken:", time.time()-t_start)

    print("Found solution:", res)
    if res:
        print(G_res.edges())
        nx.draw(G_res)
        plt.draw()
        plt.savefig("out/result_"+name+".pdf")

        # petersen = nx.petersen_graph()
        # print("Isomorphic to Petersen:", nx.is_isomorphic(G_res, petersen))



def main():
    global n, k, d, g

    # default parameters
    method = "iterative"
    stored = "continue"
    k = 3
    d = 2

    # read input
    if len(sys.argv) == 2:
        print("Usage: mooreBacktrack.py <k d> <recursive|iterative> <new|continue>")
        return

    if len(sys.argv) > 1:
        try :
            k = int(sys.argv[1])
            d = int(sys.argv[2])
            if k < 1 or d < 1:
                print("Please specify positive k and d")
                return
        except:
            print("Please specify integers k and d")
            print("Usage: mooreBacktrack.py <k d> <recursive|iterative> <new|continue>")
            return

    if len(sys.argv) > 3:
        method = sys.argv[3]
        if method != "recursive" and method != "iterative":
            print("Usage: mooreBacktrack.py <k d> <recursive|iterative> <new|continue>")
            return

    if len(sys.argv) > 4:
        stored = sys.argv[4]
        if stored != "new" and stored != "continue":
            print("Usage: mooreBacktrack.py <k d> <recursive|iterative> <new|continue>")
            return

    if len(sys.argv) > 5:
        print("Usage: mooreBacktrack.py <k d> <recursive|iterative> <new|continue>")
        return

    # update graph parameters and mode of operations
    n = k*k + 1
    g = 2*d + 1
    if stored == "new":
        stored = False
    else:
        stored = True

    do_backtrack(method, stored)

if __name__ == "__main__":
    main()