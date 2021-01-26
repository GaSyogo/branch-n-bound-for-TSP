
### tsp_bb_template_v06.py ###
# MTZ_problem，K=1

######################################################################
# A function that computes the tour length
# DON'T MODIFY THIS FUNCTION
######################################################################
def get_tour_length(n, s, D):
    import sys
    if len(s)!=n:
        sys.stderr.write('error: an infeasible tour is input to check_feasibility\n')
        sys.stderr.write('\t{}\n'.format(s))
        sys.exit(1)        
    count = [0]*n
    for k in s:
        count[k] += 1
        if count[k] == 2:
            sys.stderr.write('error: an infeasible tour is input to check_feasibility\n')
            sys.stderr.write('\t{}\n'.format(s))
            sys.exit(1)
    dist = 0
    for i in range(n-1):
        dist += D[s[i]][s[i+1]]
    dist += D[s[n-1]][s[0]]
    return dist


######################################################################
#
# Please provide your branch-and-bound algorithm in your_bb_algorithm
#
######################################################################

##### import other libraries here if necessary #####
import sys,time
import networkx as nx
import numpy as np
from pulp import *

##### please provide subroutines here if necessary #####

#def your_function():
#    pass
def nearest_n(n, D):
    root = []
    ex_root = []
    for i in range (n):
        ex_root.append(i)
    root.append(0)
    ex_root.remove(0)

    for i in range(n - 1):
        min_len = 0
        min_Num = 0
        for j in range(len(ex_root)):
            if j == 0 or min_len > D[root[i]][ex_root[j]]:
                #print (ex_root[j])
                min_len = D[root[i]][ex_root[j]]
                min_Num = ex_root[j]
        root.append(min_Num)
        ex_root.remove(min_Num)
    print("root:",root)

    return root

def opt_2(n, D, root):

    total = 0
    while True:
        count = 0
        for i in range(n - 2):
            i1 = i + 1
            for j in range(i + 2, n):
                if j == n - 1:
                    j1 = 0
                else:
                    j1 = j + 1
                if i != 0 or j1 != 0:
                    l1 = D[root[i]][root[i1]]
                    l2 = D[root[j]][root[j1]]
                    l3 = D[root[i]][root[j]]
                    l4 = D[root[i1]][root[j1]]
                    if l1 + l2 > l3 + l4:
                        new_root = root[i1:j+1]
                        root[i1:j+1] = new_root[::-1]
                        count += 1
        total += count
        print ("opt_2 root:",root)
        if count == 0: break

    return root

def MST(n,D):
    cost = 0
    G = nx.Graph()
    for i in range(n):
        for j in range(i+1):
            G.add_weighted_edges_from([(i,j,D[i][j])])
    T=nx.minimum_spanning_tree(G)
    cost = 0
    for n, nbrs in T.adj.items():
        #print("nbrs:",nbrs)
        for nbr, eattr in nbrs.items():
            if nbr < n:
                continue
            wt = eattr['weight']
            cost +=wt
            #print('(%d, %d, %.3f)' % (n, nbr, wt))
    return cost

def MTZ(n,D,E_0 = [],E_1 = []):
    cost = 0
    model = pulp.LpProblem("MTZ_problem",pulp.LpMinimize)
    Pairs = [(i,j) for i in range(n) for j in range(n)] 
    Pairs2 = [(i,j) for i in range(1,n) for j in range(1,n)]
    #Variables X_i,j in D matrix
    X = LpVariable.dicts("X",Pairs,0,1,cat = LpContinuous)
    #print('X',X)
    W = LpVariable.dicts('W',
                            (i for i in range(1,n)),
                            cat = LpContinuous)
    #print('W',W)
    # Objective function
    model += lpSum([X[(i,j)]*D[i][j] for (i,j) in Pairs])

    # Fixed constraints
    for k in range(n):
        model += lpSum([X[(k,i)] for i in range(n) if i != k]) == 1
        model += lpSum([X[(i,k)] for i in range(n) if i != k]) == 1

    for (i,j) in Pairs2:
        if i != j:
            model += W[i]-W[j]+n*X[(i,j)] <= n-1

    for i in range(n):
        model += X[(i,i)] == 0


    # Dynamic constraints because of partial solution E_0 and E_1
    #E_0
    #print("E_0 in MTZ:",E_0)
    if len(E_0) >=1:
        for k in E_0:
            #print("k:",k)
            model += X[k] == 0

    #E_1
    #print("type(E_1):",type(E_1))
    #print("E_1:",E_1)
    if len(E_1) >=1:
        i = 0
        for k in range(1,len(E_1)):
            j = E_1[k]
            model += X[i,j] == 1
            i = j

    model.solve()
    cost = value(model.objective)
    stat = model.status
    #print("stat:",stat)
    #print("After MTZ function,Status:",stat)
    #print("cost",cost)
    #tourMat = [value(X[(i,j)]) for (i,j) in Pairs]
    tourMat = np.zeros((n,n))
    for (i,j) in Pairs:
        tourMat[i][j]= value(X[(i,j)])
    #print("tourMat:",tourMat)

    return stat,cost,tourMat


def isAllInteger(M):
    for a in M:
        for b in a:
            if b%1 != 0:
                return False
    return True

def mat2sigma(M):
    n = len(M)
    print("n:",n)
    if not isAllInteger(M):
        print("the matrix is not feasible")
        sys.exit(1)
    else:
        s = []
        s.append(0)
        i = 0
        for k in range(n-1):
            for j in range(n):
                if M[i][j]==1:
                    s.append(j)
                    i = j
                    break
        return s

##### the core part of the branch-and-bound #####
def your_bb_algorithm(n,D,_start_tim,timelim):
    ##################################################
    # n: number of cities
    # D: distance matrix
    # timelim: time limit
    #
    # The function should return the incumbent solution (regardless of optimality)
    # The returned solution should be represented by a list of city indices,
    # where the city index is an integer in {0,1,...,n-1}. 
    ##################################################
    
    ##################################################
    # Please solve a relaxation problem of
    # the problem here if necessary
    ##################################################
    stat,cost,tourMat = MTZ(n,D)
    print("initial cost of MTZ as relaxation:",cost)
    if isAllInteger(tourMat):
        print("found the global optimal solution:")
        sigma_inc = mat2sigma(tourMat)
        print("sigma :",sigma_inc)
        return sigma_inc
    ##################################################
    # Please initialize sigma_inc, z_inc and L here
    # - sigma_inc: incumbent solution
    # - z_inc: objective value of sigma_inc
    # - L: list of activated subproblems
    ##################################################
    sigma_inc = nearest_n(n, D)
    sigma_inc = opt_2(n, D, sigma_inc)
    print("sigma_inc:",sigma_inc)
    z_inc = get_tour_length(n, sigma_inc, D)
    print("initial z_inc:",z_inc)
    # In this example, a subproblem is represented by
    # (E_0, E_1, length of the current path)
    # -  E_0: the list of forbidden edges
    # -  E_1: the partial solution (sequence)
    # -  if E_1=[i_1,...,i_k], then the length=D[i_1][i_2]+...+D[i_{k-1}][i_k]
    MST_cost = MST(n,D)
    print("MST_cost:",MST_cost)
    #L = [([],[0],0),] 
    L = [([],[0]),]
    ##################################################
    # DON'T MODIFY HERE
    ##################################################
    
    while L:
        _tim = time.process_time()
        if _tim-_start_tim > timelim:
            print('Warning: abort by time limit ({}>{})'.format(_tim-_start_tim,timelim))
            break

        ##################################################
        # Please provide the main part of
        # your branch-and-algorithm here
        #
        # The following is just an example and can be removed
        # It tries to construct a simple path whose length <= n-1
        ##################################################
        
        # pick up the last subproblem in the list
        (E_0,E_1) = L.pop()
        #print("E_0:",E_0)
        #print("E_1:",E_1)
        #print("lb:",lb)
        # a simple bounding operation
        stat,cost,tourMat = MTZ(n,D,E_0,E_1)
        lb = cost
        if lb>=z_inc:
            continue

        # decide the branching edge
        i = E_1[-1]
        list_i = []
        for j in range(n):
            list_i.append(tourMat[i][j])
        sort_candidate = sorted(range(len(list_i)), key=lambda k: list_i[k],reverse = True)
        for j in sort_candidate:
            if j in E_1:
                sort_candidate.remove(j)
        is_found = False
        #real_candidate = []
        for j in sort_candidate: 
            if (i,j) in E_0 or (j,i) in E_0:
                continue
            if tourMat[i][j] == 0:
                continue
            is_found = True
            #real_candidate.append(j)
            real_candidate = j

        #print("real_candidate:",real_candidate)

        if not is_found:
            continue

        '''
        r = len(real_candidate)
        for k in range(r+1):
            add2E_1 = []
            if k == 0:
                stat,cost,tourMat = MTZ(n,D,list(E_0+[(i,real_candidate[k])]),E_1)
                if stat < 0 or cost >= z_inc:
                    pass
                elif isAllInteger(tourMat):
                    if cost < z_inc:
                        sigma_inc = mat2sigma(tourMat)
                        z_inc = cost
                        print('z_inc:\t{}\t{:.4f}\t{}'.format(z_inc, _tim-_start_tim, sigma_inc))
                else:
                    L.append((list(E_0+[(i,real_candidate[k])]),list(E_1)))

            elif k >= 1 and k <= (r-1):
                for l in range(k):
                    add2E_1.append(real_candidate[l])
                stat,cost,tourMat = MTZ(n,D,list(E_0+[(i,real_candidate[k])]),list(E_1+add2E_1))
                if stat < 0 or cost >= z_inc:
                    pass
                elif isAllInteger(tourMat):
                    if cost < z_inc:
                        sigma_inc = mat2sigma(tourMat)
                        z_inc = cost
                        print('z_inc:\t{}\t{:.4f}\t{}'.format(z_inc, _tim-_start_tim, sigma_inc))
                else:
                    L.append((list(E_0+[(i,real_candidate[k])]),list(E_1+add2E_1)))

            else:# k=r
                for l in range(k):
                    add2E_1.append(real_candidate[l])
                stat,cost,tourMat = MTZ(n,D,list(E_0),list(E_1+add2E_1))
                if stat < 0 or cost >= z_inc:
                    pass
                elif isAllInteger(tourMat):
                    if cost < z_inc:
                        sigma_inc = mat2sigma(tourMat)
                        z_inc = cost
                        print('z_inc:\t{}\t{:.4f}\t{}'.format(z_inc, _tim-_start_tim, sigma_inc))
                else:
                    L.append((list(E_0),list(E_1+add2E_1)))
        '''
        
        # two subproblems are generated according to whether {i,j} is included or not
        j = real_candidate
        # case 1: (i,j) is not included
        stat,cost,tourMat = MTZ(n,D,list(E_0+[(i,j)]),E_1)
        if stat < 0 or cost >= z_inc:
            pass
        elif isAllInteger(tourMat):
            if cost < z_inc:
                sigma_inc = mat2sigma(tourMat)
                z_inc = cost
                print('z_inc:\t{}\t{:.4f}\t{}'.format(z_inc, _tim-_start_tim, sigma_inc))
        else:
            L.append((list(E_0+[(i,j)]), list(E_1)))

        # case 2: (i,j) is included; in this case, we should update the incumbent solution if necessary
        stat,cost,tourMat = MTZ(n,D,E_0,list(E_1+[j]))
        if stat < 0 or cost >= z_inc:
            pass
        elif isAllInteger(tourMat):
            if cost < z_inc:
                sigma_inc = mat2sigma(tourMat)
                z_inc = cost
                print('z_inc:\t{}\t{:.4f}\t{}'.format(z_inc, _tim-_start_tim, sigma_inc))
        else:
            L.append((list(E_0), list(E_1+[j])))
        
        
    ##################################################
    # DON'T MODIFY HERE
    ##################################################
    return sigma_inc
    
######################################################################
#
# DON'T MODIFY BELOW
#
######################################################################

timelim = 180

def read_instance():
    try:
        n = int(input())
        D = []
        for i in range(n):
            s = input().split(' ')
            a = tuple(map(int, s))
            D.append(a)
        #print(D)
        return(n,D)

    except:
        sys.stderr.write('error: failed to read the instance from stdin.\n')
        exit(1)

        
def main():
    (n,D) = read_instance()
    _start_tim = time.process_time()
    sigma = your_bb_algorithm(n,D,_start_tim,timelim)
    print("sigma:",sigma)
    obj = get_tour_length(n,sigma,D)
    print('objective value: {}'.format(obj))
    print('computation time: {}'.format(time.process_time()-_start_tim))
    
    
if __name__ == "__main__":
    main()
