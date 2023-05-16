//
/*
I realized reading data from stdin in Python is much slower than in CPP
so I switched from Python code to CPP. Thank Phan Phan Hai Long 20214964 for helping me transfer code
2-OPT, 3-OPT, POPMUSIC...: Éric D. Taillard, Design of Heuristic Algorithms for Hard Optimization, https://doi.org/10.1007/978-3-031-13714-3
*/
//
#include <iostream>
#include <random>
#include <utility>
#include <vector>
using namespace std;
//int N, K;
int N, K;
long dist[2000][2000];


void input_data(){
    cin >> N >> K;
    for(int i = 0; i <= N; i++){
        for(int j = 0; j <= N; j++){
            cin >> dist[i][j];
        }
    }
}

//Returns a random integer in [a; b]
int rand_int(int a, int b){
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> dis(a, b);
    return dis(gen);
}

//Returns a random permutation of the elements 0...n-1
vector<int> rand_permutation(int n){
    vector<int> a(n);
    for(int i = 0; i < n; i++){
        a[i] = i;
    }
    for(int i = 0; i < n; i++){
        int j = rand_int(i, n - 1);
        swap(a[i], a[j]);
    }
    return a;
}


//compute the length of each route in tour
vector<long> vrp_route_length(vector<vector<int>> tour){
    vector<long> route_length(K+1);
    for (int k = 1; k < K+1; k++){
        unsigned n = tour[k].size();
        long s = dist[tour[k][-1]][0];
        for(int j = 0; j < N-1; j++){
            s += dist[tour[k][j]][tour[k][j+1]];
        }
        route_length[k] = s;
    }
    return route_length;
}

//compute the total length of tour
long vrp_tour_length(vector<vector<int>> tour){
    vector<long> route_length = vrp_route_length(std::move(tour));
    long s = 0;
    for(int i = 1; i < K+1; i++){
        s += route_length[i];
    }
    return s;
}

//# compute the length of a tsp tour
long tsp_length(vector<int> tour){
    unsigned n = tour.size();
    long s = dist[tour[n-1]][tour[0]];
    for(int i = 0; i < n-1; i++){
        s += dist[tour[i]][tour[i+1]];
    }
    return s;
}

//# build solution representation by successors
vector<int> tsp_tour_to_successor(vector<int> tour){
    unsigned n = tour.size();
    vector<int> successor(n);
    for(int i = 0; i < n-1; i++){
        successor[tour[i]] = tour[i + 1];
    }
    successor[tour[n - 1]] = tour[0];
    return successor;
}


//build solution representation by predeccessors
vector<int> tsp_successor_to_pred(vector<int> successor){
    unsigned n = successor.size();
    vector<int> pred(n);
    for(int i = 0; i < n; i++){
        pred[successor[i]] = i;
    }
    return pred;
}

//convert solution from successor of each city to city order
vector<int> tsp_successor_to_tour(vector<int> successor){
    int n = successor.size();

    vector<int> tour(n);
    int j = 0;
    for(int i = 0; i < n; i++){
        tour[i] = j;
        j = successor[j];
    }
    return tour;
}

//# convert a solution given by 2-opt data structure to a standard tour
vector<int> tsp_2opt_data_structure(vector<int> t){
    int n = static_cast<int>(t.size() / 2.0 + 0.5);
    vector<int> tour(n);
    int j = 0;
    for(int i = 0; i < n; i++){
        tour[i] = j >> 1;
        j = t[j];
    }
    return tour;
}

//# data structure building for performing 2-opt move in constant time
vector<int> build_2opt_data_structure(vector<int> tour){
    unsigned n = tour.size(); //# order of visit of the cities
    vector<int> t(n * 2);
    for(int i = 0; i < n-1; i++){
        t[2 * tour[i]] = 2 * tour[i+1];
    }
    t[2 * tour[n-1]] = 2 * tour[0];
    for(int i = 1; i < n; i++){
        t[2 * tour[i] + 1] = 2 * tour[i-1] + 1;
    }
    t[2 * tour[0] + 1] = 2 * tour[n-1] + 1;
    return t;
}

//# local search with 2-opt neighborhood and first improvement policy
vector<int> tsp_2opt_first(vector<int> tour, int *length){
    unsigned n = tour.size();
    int &len = *length;
    vector<int> t = build_2opt_data_structure(tour);
    long i = 0, last_i = 0; //# i = starting city || last_i = i - a complete tour
    while (t[t[i]] >> 1 != last_i){ // index i has made 1 turn without improvement
        long j = t[t[i]];
        while ((j >> 1 != last_i) && ((t[j] >> 1 != last_i) || (i >> 1 != last_i))){
            long delta = dist[i >> 1][j >> 1] + dist[t[i] >> 1][t[j] >> 1] - dist[i >> 1][t[i] >> 1] - dist[j >> 1][t[j] >> 1];
            if(delta < 0){ //# An improving move is found
                long next_i = t[i];
                long next_j = t[j];
                t[i] = j ^ 1;
                t[j] = i ^ 1;
                t[next_i ^ 1] = next_j;
                t[next_j ^ 1] = next_i;
                len += delta;
                last_i = i >> 1; //# Solution improved: i must make another turn
                j = t[i];
            }
            j = t[j];
        }
        i = t[i];
    }
    return tsp_2opt_data_structure(t);
}


//### POPMUSIC (Partial Optimization Metaheuristic Under Special Intensification Condition)
vector<int> tsp_3opt_limited(vector<int> succ, int sub_size, int *length){
    // succ: Tour provided and returned (represented by successors)
    // sub_size: subproblem size
    // length: tour length
    int n = succ.size();
    int &len = *length;
    if (sub_size > n - 2){ //# Subproblem size must not exceed n - 2
        sub_size = n - 2;
    }
    int i = 0, last_i = 0; //# starting city is index 0
    while (true){
        int j = succ[i];
        int t = 0;
        // do not exceed subproblem and the limits of the neighborhood
        while ((t<sub_size) && (succ[succ[j]] != last_i)){
            long k = succ[j];
            int u = 0;
            while ((u<sub_size) && (succ[k] != last_i)){
                long delta = dist[i][succ[j]] + dist[j][succ[k]] + dist[k][succ[i]] - dist[i][succ[i]] - dist[j][succ[j]] - dist[k][succ[k]];
                if (delta < 0){ //# Is there an improvement?
                    // succ[i], succ[j], succ[k] = succ[j], succ[k], succ[i]
                    //# Perform move
                    int temp = succ[i];
                    succ[i] = succ[j];
                    succ[j] = succ[k];
                    succ[k] = temp;
                    len += delta;
                    last_i = i;

                    temp = j;
                    j = k;
                    k = temp;
                }
                u += 1;
                k = succ[k]; // Next k
        }
            t += 1;
            j = succ[j]; // Next j
        }
        i = succ[i]; // Next i
        if (i == last_i){ //# A complete tour scanned without improvement
            break;
        }

    
    }
return succ;
}


//Local search with 3-opt neighborhood and first improvement policy

vector<int> tsp_3opt_first(vector<int> succ, int *length){
    long last_i = 0;
    long last_j = succ[0];
    long last_k = succ[succ[0]];
    long i = last_i;
    long j = last_j;
    long k = last_k;
    int &len = *length;
    while (true){
        long delta = dist[i][succ[j]] + dist[j][succ[k]] + dist[k][succ[i]] - dist[i][succ[i]] - dist[j][succ[j]] - dist[k][succ[k]];
        if (delta < 0){ //# is there an improvement?
            
            //# Perform move
            int temp = succ[i];
            succ[i] = succ[j];
            succ[j] = succ[k];
            succ[k] = temp;

            // # Replace j between i and k
            temp = j;
            j = k;
            k = temp;

            len += delta; //# Update solution cost
            last_i = i;
            last_j = j;
            last_k = k;
        }
        k = succ[k]; // Next k
        if (k == i){ //# k at its last value, next j
            j = succ[j];
            k = succ[j];
        }
        if (k == i){ //# j at its last value, next i
            i = succ[i];
            j = succ[i];
            k = succ[j];
        }
        if ((i == last_i) && (j == last_j) && (k == last_k)){
            break;
        }
    }
    return succ;
}

vector<vector<int>> greedy_optimalTSPtoVRP(vector<int> solution, int *length)
{

    int &len = *length;
    vector<vector<int>> tour{{}};
    vector<long> route_length(K+1);

    for(int i=0; i<K; i++)
    {
        tour.push_back({0});
    }



    for(int i=1; i<K+1;i++)
    {
        route_length[i] = 0;
    }


    int k=1;
    int i=1;
    while (k<K)
    {
        route_length[k] = route_length[k] + dist[tour[k][tour[k].size()-1]][solution[i]];

        tour[k].push_back(solution[i]);

        i = i+1;


        while (route_length[k] + dist[tour[k][tour[k].size()-1]][solution[i]] - dist[0][tour[k][1]]<= len/static_cast<float>(K))
        {

            route_length[k] = route_length[k] + dist[tour[k][tour[k].size()-1]][solution[i]];
            tour[k].push_back(solution[i]);
            i += 1;
            if (i>N) break;
            if (route_length[k] + dist[tour[k][tour[k].size()-1]][solution[i]] - dist[0][tour[k][1]]> len/static_cast<float>(K))
            {

                k += 1;
                break;
            }
            if (k>K-1) break;


        }

    }
    for(int j=i; j<N+1; j++)
    {
        tour[k].push_back(solution[j]);
    }
    return tour;
}

void printSolution(vector<vector<int>> tour)
{
    cout <<K<<"\n";
    for(int k=1; k<=K; k++)
    {
        cout<<tour[k].size() <<"\n";
        for(int j=0; j < tour[k].size(); j++)
        {
            cout<< tour[k][j] <<" ";
        }
        cout<<"\n";
    }
}


int main(){
    input_data();
    int n = N+1;


    
    vector<int> solution = rand_permutation(n);
    int length = tsp_length(solution);

    solution = tsp_2opt_first(solution, &length);

    vector<int> succ = tsp_tour_to_successor(solution);




    
    if (n>100){
    succ = tsp_3opt_limited(succ, 25, &length);
    }
    else succ = tsp_3opt_first(succ, &length);
    
    solution = tsp_successor_to_tour(succ);

    vector<vector<int>> tour = greedy_optimalTSPtoVRP(solution, &length);

    /*
    for(int i=1; i < K+1; i++)
    {
        for(int j=0; j<tour[i].size(); j++)
        {
            cout << tour[i][j] << " ";
        }
        cout <<"\n";
    }

    vector<long> route_length = vrp_route_length(tour);
    cout<<"route_length = \n";
    for(int i=1; i <=K; i++) cout <<route_length[i] <<" ";
    cout <<"\n";
    */
    printSolution(tour);
    return 0;

}





