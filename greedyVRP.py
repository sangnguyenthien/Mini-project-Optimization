# Python code for Greedy algorithm is made by Nguyễn Thiện Sang 20214972 - Group 1
# Python code for 2-OPT, 3-OPT, POPMUSIC...: Éric D. Taillard, Design of Heuristic Algorithms for Hard Optimization, https://doi.org/10.1007/978-3-031-13714-3
import copy
import time
import sys




def rando():
    m, m2 = 2147483647, 2145483479
    a12, a13, a21, a23 = 63308, -183326, 86098, -539608
    q12, q13, q21, q23 = 33921, 11714, 24919, 3976
    r12, r13, r21, r23 = 12979, 2883, 7417, 2071
    invm = 4.656612873077393e-10
    h = rando.x10 // q13
    p13 = -a13 * (rando.x10 - h * q13) - h * r13
    h = rando.x11 // q12
    p12 = a12 * (rando.x11 - h * q12) - h * r12
    if p13 < 0: p13 = p13 + m
    if p12 < 0: p12 = p12 + m
    rando.x10, rando.x11, rando.x12 = rando.x11, rando.x12, p12 - p13
    if rando.x12 < 0: rando.x12 = rando.x12 + m
    h = rando.x20 // q23
    p23 = -a23 * (rando.x20 - h * q23) - h * r23
    h = rando.x22 // q21
    p21 = a21 * (rando.x22 - h * q21) - h * r21
    if p23 < 0: p23 = p23 + m2
    if p21 < 0: p21 = p21 + m2
    rando.x20, rando.x21, rando.x22 = rando.x21, rando.x22, p21 - p23
    if rando.x22 < 0: rando.x22 = rando.x22 + m2
    if rando.x12 < rando.x22: h = rando.x12 - rando.x22 + m
    else: h = rando.x12 - rando.x22
    if h == 0: return 0.5
    else: return h * invm

rando.x10, rando.x11, rando.x12 = 12345, 67890, 13579
rando.x20, rando.x21, rando.x22 = 24680, 98765, 43210





def inputFromFile(filename):
    with open(filename, "r") as f:
        lines = f.readlines()
        [N, K] = [int(x) for x in lines[0].split()]
        distances = []
        for i in range(1, N+2):
            distances.append([int(x) for x in lines[i].split()])
    return N, K, distances



def input_():
    [N, K] = [int(x) for x in sys.stdin.readline().split()]
    d = []
    for i in range(N+1):
        r = [int(x) for x in sys.stdin.readline().split()]
        d.append(r)
    return N, K, d



def writeSolution(filename, tour, K):
    with open(filename, "w") as f:
        f.write(str(K))
        f.write("\n")
        result = ''
        for k in range(1, K+1):
            s = str(len(tour[k])) + '\n'
            for i in tour[k]:
                s = s + str(i) + ' '
            s = s + '\n'
            result += s
        f.write(result)
        f.close()

def printSolution(tour, K):
    print(K)
    for k in range(1, K+1):
        print(len(tour[k]))
        print(' '.join(str(x) for x in tour[k]))



######## Returns a random integer in [low; high]
def unif(low, high):
    return low + int((high - low + 1) * rando())

######## Returns a random permutation of the elements 0...n-1
def rand_permutation(n):
    p = [i for i in range(n)]
    for i in range(n - 1):
        random_index = unif(i, n - 1)
        p[i], p[random_index] = p[random_index], p[i]
    return p



##### compute the length of each route in tour
def vrp_route_length(d, K, tour):

    route_length = [[]]
    for k in range(1, K+1):
        #print('k=',k)
        #print(len(tour))
        n = len(tour[k])
        s = d[tour[k][n-1]][0]
        for i in range(n-1):
            s += d[tour[k][i]][tour[k][i+1]]
        route_length.append(s)
    return route_length

#### compute the total length of tour
def vrp_tour_length(d, K, tour):
    return sum(vrp_route_length(d, K, tour)[1:]) #type: ignore







# compute the length of a tsp tour
def tsp_length(d, tour):
    n = len(tour)
    length = d[tour[n-1]][tour[0]]
    for i in range(n-1):
        length += d[tour[i]][tour[i+1]]
    return length

# build solution representation by successors
def tsp_tour_to_succ(tour):
    #print(n)
    n = len(tour)
    #print(n)
    succ = [-1] * n
    for i in range(n):
        succ[tour[i]] = tour[(i+1)%n]
    return succ

# build solution representation by predeccessors
def tsp_succ_to_pred(succ):
    n = len(succ)
    pred = [-1]*n
    for i in range(n):
        pred[succ[i]] = i
    return pred

# convert solution from successor of each city to city order
def tsp_succ_to_tour(succ):
    n = len(succ)
    print('succ = ', succ)

    tour = [-1]*n
    j = 0
    for i in range(n):
        tour[i] = j
        j = succ[j]
    return tour

# convert a solution given by 2-opt data structure to a standard tour
def tsp_2opt_data_structure_to_tour(t):
    n = int(len(t)/2 + 0.5)
    tour = [-1]*n
    j = 0
    for i in range(n):
        tour[i] = j >> 1
        j = t[j]
        #print('tour =', tour)
        #print('t =', t)
        #print('j = ', j)
    return tour

# compare 2 directed tours; returns the number of different arcs
def tsp_compare(succ_a, succ_b):
    n = len(succ_a)
    count = 0
    for i in range(n):
        if succ_a[i] != succ_b[i]:
            count += 1
    return count


# data structure building for performing 2-opt move in constant time
def build_2opt_data_structure(tour): # order of visit of the cities
    n = len(tour)
    t = [-1]*2*n
    for i in range(n-1):
        t[2*tour[i]] = 2*tour[i+1]
    t[2*tour[n-1]] = 2* tour[0]
    for i in range(1, n):
        t[2*tour[i]+1] = 2*tour[i-1] + 1
    t[2*tour[0] + 1] = 2 * tour[n-1] + 1
    return t

# local search with 2-opt neighborhood and first improvement policy
def tsp_2opt_first(d, tour, length):
    n = len(tour)
    t = build_2opt_data_structure(tour)
    i = last_i = 0 # i = starting city || last_i = i - a complete tour
    while t[t[i]] >> 1 != last_i: # index i has made 1 turn without improvement
        j = t[t[i]]
        while j >> 1 != last_i and (t[j] >> 1 != last_i or i >> 1 != last_i):
            delta = d[i>>1][j>>1] + d[t[i]>>1][t[j]>>1] \
                - d[i>>1][t[i]>>1] - d[j>>1][t[j]>>1]
            if delta < 0: # An improving move is found
                next_i, next_j = t[i], t[j] # Perform move
                t[i], t[j] = j ^ 1, i ^ 1
                t[next_i ^ 1], t[next_j ^ 1] = next_j, next_i

                length += delta # Update solution cost
                #print('delta =', delta)
                #print('length =', length)
                last_i = i >> 1 # Solution improved: i must make another turn
                j = t[i]
            j = t[j]
        i = t[i]
        #print('length =', length)
    return tsp_2opt_data_structure_to_tour(t), length


### POPMUSIC (Partial Optimization Metaheuristic Under Special Intensification Condition)
def tsp_3opt_limited(d, # Distance matrix
    r, # Subproblem size
    succ, # Tour provided and returned
    length): # Tour length
    n = len(succ)
    if r > n - 2: # Subproblem size must not exceed n - 2
        r=n-2
    i = last_i = 0 # starting city is index 0
    while True:
        j = succ[i]
        t=0
        # do not exceed subproblem and the limits of the neighborhood
        while t<r and succ[succ[j]] != last_i:
            k = succ[j]
            u=0
            while u<r and succ[k] != last_i:
                delta = d[i][succ[j]] + d[j][succ[k]] + d[k][succ[i]] \
                        -d[i][succ[i]] - d[j][succ[j]] - d[k][succ[k]]
                if delta < 0: # Is there an improvement?
                    length += delta # Perform move
                    succ[i], succ[j], succ[k] = succ[j], succ[k], succ[i]
                    j, k = k, j # Replace j between i and k
                    last_i = i
                u += 1
                k = succ[k] # Next k
            t += 1
            j = succ[j] # Next j
        i = succ[i] # Next i

        if i == last_i: # A complete tour scanned without improvement
            break

    return succ, length







######### Local search with 3-opt neighborhood and first improvement policy
def tsp_3opt_first(d, succ, length):
    last_i, last_j, last_k = 0, succ[0], succ[succ[0]]
    i, j, k = last_i, last_j, last_k
    while True:
        delta = d[i][succ[j]] + d[j][succ[k]] + d[k][succ[i]] \
            -d[i][succ[i]] - d[j][succ[j]] - d[k][succ[k]] # Move cost
        if delta < 0: # is there an improvement?
            length += delta # Update solution cost
            succ[i], succ[j], succ[k] = succ[j], succ[k], succ[i]# Perform move
            j, k = k, j      # Replace j between i and k
            last_i, last_j, last_k = i, j, k
        k = succ[k]    #next k
        if k == i: # k at its last value, next j
            j = succ[j]; k = succ[j]
        if k == i: # j at its last value, next i
            i = succ[i]; j = succ[i]; k = succ[j]
        if i == last_i and j == last_j and k == last_k:
            break
        
        #print('length =', length)
    return succ, length


def greedy_optimalTSPtoVRP(solution, length, N, K, distances):
    solution, length = tsp_2opt_first(distances, solution, length)
    #print('Cost of solution found with 2-opt first: {:d}'.format(length))
    print("solution =", solution)
    
    succ = tsp_tour_to_succ(solution)
    succ, length = tsp_3opt_limited(distances, 25, succ, length)


    solution = tsp_succ_to_tour(succ)
    #print('Cost of solution found with 2-opt first and 3-opt limited: {:d}'.format(length))
    


    '''
    successors = tsp_tour_to_succ(solution)
    
    successors, length = tsp_3opt_first(distances, successors, length)
    solution = tsp_succ_to_tour(successors)
    print('Solution improved with 3-opt first: {:d}'.format(length))
    '''
    
    
    ####### transform TSP tour to VRP tour (greedy)
    tour = [[]]
    for i in range(K):
        tour.append([0])
    route_length = [0]
    for i in range(K):
        route_length.append(0)
    #print(route_length)
    k = 1
    i = 1
    while k < K:
        route_length[k] = route_length[k] + distances[tour[k][len(tour[k])-1]][solution[i]]
        tour[k].append(solution[i])
        i = i + 1
        while route_length[k] + distances[tour[k][len(tour[k])-1]][solution[i]] - distances[0][tour[k][1]]<= length/K:
            #print(route_length)
            #tour[k].append(solution[i])
            route_length[k] = route_length[k] + distances[tour[k][len(tour[k])-1]][solution[i]]
            tour[k].append(solution[i])
            i += 1
            if i > N:
                break
            #print(i)
            if route_length[k] + distances[tour[k][len(tour[k])-1]][solution[i]] - distances[0][tour[k][1]]> length/K:
                k += 1
                break
            if k > K-1:
                break

    for j in range(i, N+1):
        tour[k].append(solution[j])
    
    #route_length = vrp_route_length(distances, tour)
    #tour_length = vrp_tour_length(distances, tour)
    #print('route_length = ', route_length)
    #print('length =', tour_length)
    route_length = vrp_route_length(distances, K, tour)
    tour_length = vrp_tour_length(distances, K, tour)
    return tour, route_length, tour_length

###########################################################




def main():
    ########## inputFromFile(filename)
    #N, K, distances = inputFromFile("C:\\Users\\admin\\OneDrive\\Máy tính\\Mini-project\\input\\1000_20.txt")

    #N, K, distances = inputFromFile("test.in")


    #start_time = time.time()
    N, K, distances = input_()
    #execution_time = time.time() - start_time
    #print("Execution time: ", execution_time)


    n = N+1

    solution = rand_permutation(n)
    length = tsp_length(distances, solution)

    #start_time = time.time()
    tour, route_length, tour_length = greedy_optimalTSPtoVRP(solution, length, N, K, distances)


    ####### writeSolution(filename, tour)
    #writeSolution("test.out", tour, K)

    #print("done")
    printSolution(tour, K)

if __name__ == "__main__":
    main()







