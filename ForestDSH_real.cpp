//
//  main.cpp
//  DSHTree
//
//  Created by Sean Chang on 4/25/19.
//  Copyright © 2019 Sean Chang. All rights reserved.
//

#include <iostream>
#include <cstdlib>
#include <math.h>
#include <cmath>
#include <string>
#include <vector>
#include <sstream>
#include <fstream>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <chrono>

typedef std::chrono::high_resolution_clock Clock;

//Keeping track of the number of accepts, rejects, alpha, and beta
int accepts = 0;
int rejects = 0;
double TFP = 0.0;
double TTP = 0.0;
double gx = 0.0;
double gy = 0.0;
int totalX = 0;
int totalY = 0;

//Debugging purposes
int numNodes = 0;
int xnodes = 0;
int ynodes = 0;
int deepest = 0;

//Toggle this boi
double C1;

double p1;
double p2;
double p3;
double p4;

std::vector<bool> found;
int unique;
std::vector<std::vector<bool>> ufp;
int funique;

//2D vector that holds doubles
typedef std::vector<std::vector<double>> arr;
typedef std::vector<std::vector<long double>> larr;

//p and q are 2D vectors that represent a probability matrix
struct probs_header {
    larr p, q;
    std::vector<long double> px, py, qx, qy;
};
typedef struct probs_header probs;

//Special string structure so we can tell which string is paired with which string
struct istring {
    std::string str;
    int id;
};

//Represents a bucket
//xstr and ystr are the strings at that bucket.
//xmatches and ymatches represent the strings that go into the bucket.
struct bucket {
    std::string xstr, ystr;
    std::vector<istring*> xmatches, ymatches;
};

//Tree node
//Contains a vector of its children, what string it represents, and all the buckets at that node
struct tnode {
    std::vector<tnode*> children;
    std::string str;
    std::vector<bucket*> bvec;
};

//Copied from common_funcs.cpp
//Xcode linker why don't you work
#define MODULO 100000

// Initial random seed
int init_seed = 420;

int my_rand(int *x) {
    long long tmp = *x;
    long long lol = 1 << 31;
    long long tmp2 = (tmp * 48271) % (lol - 1);
    *x = int(tmp2);
    return int(tmp2);
}

//Copied from common_funcs.cpp
std::vector <int> get_permut(int T, int seed) {
    
    std::vector <int> permut;
    for (int i = 0; i < T; i++) permut.push_back(i);
    
    for (int i = T-1; i > 0; i--) {
        int rand_num = my_rand(&seed) % i;
        std::swap(permut[i], permut[rand_num]);
    }
    return permut;
}

//Compute the q matrix given the p matrix and set up a probability distribution with them
probs* set_pq_values(larr pmatrix) {
    
    probs *ret = new probs();
    larr qmatrix;
    
    ret -> p = pmatrix;
    
    std::vector<long double> rowsums(pmatrix.size(), 0.0);
    std::vector<long double> colsums(pmatrix.size(), 0.0);
    
    for(int i = 0; i < pmatrix.size(); i++) {
        for(int j = 0; j < pmatrix.size(); j++) {
            rowsums.at(i) += pmatrix.at(i).at(j);
            colsums.at(j) += pmatrix.at(i).at(j);
        }
    }
    
    ret -> px = rowsums;
    ret -> py = colsums;
    
    for(int i = 0; i < pmatrix.size(); i++) {
        std::vector<long double> newrow;
        for(int j = 0; j < pmatrix.size(); j++) {
            newrow.push_back(rowsums.at(i) * colsums.at(j));
        }
        qmatrix.push_back(newrow);
    }
    
    ret -> q = qmatrix;
    
    std::vector<long double> qx(qmatrix.size(), 0.0);
    std::vector<long double> qy(qmatrix.size(), 0.0);
    
    for(int i = 0; i < qmatrix.size(); i++) {
        for(int j = 0; j < qmatrix.size(); j++) {
            qx.at(i) += qmatrix.at(i).at(j);
            qy.at(j) += qmatrix.at(i).at(j);
        }
    }
    
    ret -> qx = qx;
    ret -> qy = qy;
    
    return ret;
}

//Should we accept as a bucket?
bool accept(int N, double lstar, double P, double Q) {
    return P / Q >= pow(N, 1 + 1 - lstar) * p1;
}

bool reject(double P, double Qx, double Qy, int N, double mu, double nu, double b, double lstar) {
    return P/Qx < pow(N, 1 - lstar) * p2 || P/Qy < pow(N, 1 - lstar) * p3 /*||  pow(P, 1 + mu + nu - b) * pow(Qx, -1 * mu) * pow(Qy, -1 * nu) < pow(N, -1 * lstar) * p4*/;
}

//Given R and tne corresponding P and Q values, calculate rij
double computerij(double R, double pij, double qij, double l1, double l2) {
    return R * pow(pij, l1) * pow(qij, l2);
}

//We do this computation a lot so it gets it's own function
double Fsum(probs* prob, double mu, double t) {
    double count = 0.0;
    for(int i = 0; i < (prob -> p).size(); i++) {
        for(int j = 0; j < (prob -> p).size(); j++) {
            count += pow((prob -> p).at(i).at(j), mu + 1) * pow((prob -> q).at(i).at(j), t);
        }
    }
    return count;
}

//Approximate t with Newton's method
double approxT(probs* prob, double mu) {
    double t = 0.0;
    
    //Newton's method
    //Shouldn't be anything greater than 30
    for(int i = 0; i < 30; i++) {
        double slope = 0.0;
        for(int k = 0; k < (prob -> p).size(); k++) {
            for(int j = 0; j < (prob -> p).size(); j++) {
                //if((prob -> q).at(i).at(j) != 0) {
                slope += pow((prob -> p).at(k).at(j), mu + 1) * pow((prob -> p).at(k).at(j), t) * log((prob -> q).at(k).at(j));
                //}
            }
        }
        double current = Fsum(prob, mu, t);
        double deltaT = (current - 1) / slope;
        double t_old = t;
        t -= deltaT;
        //Line search if necessary
        int itr = 0;
        double updated = Fsum(prob, mu, t);
        while(abs(current - 1) < abs(updated - 1) && itr < 1000) {
            t = (t + t_old) / 2;
            updated = Fsum(prob, mu, t);
            itr++;
        }
    }
    return t;
}

std::vector<long double> geometricLambda(probs *P) {
    std::vector<long double> info;
    long double mustar = -1;
    long double nustar = -1;
    long double etastar = -1;
    long double lambdastar = -1;
    int numRows = (int)(P -> p).size();
    int numCols = (int)(P -> p).at(0).size();
    for(long double mu = 0.001; mu < 1000; mu *= 1.1) {
        for(long double nu = 0.001; nu < 1000; nu *= 1.1) {
            long double val = 50;
            long double eta = mu;
            if(nu < mu) {
                eta = nu;
            }
            while(val >= 1.001) {
                val = 0.0;
                for(int row = 0; row < numRows; row++) {
                    for(int col = 0; col < numCols; col++) {
                        if((P -> p).at(row).at(col) > 0.000001) {
                            val += pow((P -> p).at(row).at(col), 1 + mu + nu - eta) * pow((P -> px).at(row), -1 * (mu)) * pow((P -> py).at(col), -1 * (nu));
                        }
                    }
                }
                if(val >= 0.999 && val <= 1.001) {
                    long double lambda = (1 + mu + nu) / (1 + mu + nu - eta);
                    if(lambda > lambdastar) {
                        mustar = mu;
                        nustar = nu;
                        etastar = eta;
                        lambdastar = lambda;
                    }
                }
                eta = eta/1.1;
            }
        }
    }
    info.push_back(mustar);
    info.push_back(nustar);
    info.push_back(etastar);
    info.push_back(lambdastar);
    //std::cout << "max loop: " << maxloop << "\n";
    return info;
}

//The probability that x and y were generated given p
double matchProbability(probs *prob, std::string x, std::string y) {
    double product = 1.0;
    for(int i = 0; i < x.length(); i++) {
        int xind = std::stoi(x.substr(i, 1));
        int yind = std::stoi(y.substr(i, 1));
        product *= (prob -> p).at(xind).at(yind);
    }
    return product;
}

double matchProbabilityQ(probs *prob, std::string x, std::string y) {
    double product = 1.0;
    for(int i = 0; i < x.length(); i++) {
        int xind = std::stoi(x.substr(i, 1));
        int yind = std::stoi(y.substr(i, 1));
        product *= (prob -> q).at(xind).at(yind);
    }
    return product;
}

//Recursive call for generating a tree
void generateTreeHelper(probs* prob, double oldP, double oldQ, double qx, double qy, double gamma_x, double gamma_y, int xind, int yind, int N, std::vector<long double> info, tnode *xtree, tnode *ytree) {
    
    //Debugging purposes
    numNodes++;
    
    //Update the probabilities
    double newP = oldP * (prob -> p).at(xind).at(yind);
    double newQ = oldQ * (prob -> q).at(xind).at(yind);
    double newqx = qx * (prob -> qx).at(xind);
    double newqy = qy * (prob -> qy).at(yind);
    double newgamma_x = gamma_x * (prob -> px).at(xind);
    double newgamma_y = gamma_y * (prob -> py).at(yind);

    //Create new nodes if they don't already exist
    if((xtree -> children).at(xind) == NULL) {
        tnode *newX = new tnode();
        newX -> str = (xtree -> str) + std::to_string((long long int)xind);
        for(int i = 0; i < (prob -> p).size(); i++) {
            (newX -> children).push_back(NULL);
        }
        (xtree -> children).at(xind) = newX;
        xnodes++;
    }
    if((ytree -> children).at(yind) == NULL) {
        tnode *newY = new tnode();
        newY -> str = (ytree -> str) + std::to_string((long long int)yind);
        for(int i = 0; i < (prob -> p).size(); i++) {
            (newY -> children).push_back(NULL);
        }
        (ytree -> children).at(yind) = newY;
        ynodes++;
    }
    
    //These are the nodes that we are looking at in this call
    tnode* currX = (xtree -> children).at(xind);
    tnode* currY = (ytree -> children).at(yind);
    
    //Check for acceptance
    if(accept(N, info.at(3), newP, newQ)) {
        //Create a newbucket
        bucket *nb = new bucket();
        nb -> xstr = currX -> str;
        nb -> ystr = currY -> str;
        //std::cout<<currX -> str<<" "<<currY -> str<<"\n";
        currX -> bvec.push_back(nb);
        currY -> bvec.push_back(nb);
        
        //Update number of accepts, alpha, and beta
        accepts++;
        TFP += newQ;
        TTP += newP;
        
        gx += newgamma_x;
        gy += newgamma_y;
        
        if((currX -> str).length() > deepest) {
            deepest = (int)(currX -> str).length();
        }
        return;
    }
    //Check for rejection
    else if(reject(newP, newqx, newqy, N, info.at(0), info.at(1), info.at(2), info.at(3))) {
        //Update number of rejections
        rejects++;
        return;
    }
    else {
        //Recursive calls.
        for(int i = 0; i < (prob -> p).size(); i++) {
            for(int j = 0; j < (prob -> p).size(); j++) {
                generateTreeHelper(prob, newP, newQ, newqx, newqy, newgamma_x, newgamma_y, i, j, N, info, currX, currY);
            }
        }
        return;
    }
}

//Create the root and recursively generate the tree
std::pair<tnode*, tnode*> generateTree(probs* prob, int N, std::vector<long double> info) {
    //Setting up the root stuff
    tnode *xtree = new tnode();
    xtree -> str = "";
    tnode *ytree = new tnode();
    ytree -> str = "";
    for(int i = 0; i < (prob -> p).size(); i++) {
        (xtree -> children).push_back(NULL);
        (ytree -> children).push_back(NULL);
    }
    
    //Recursively generate the tree.
    for(int i = 0; i < (prob -> p).size(); i++) {
        for(int j = 0; j < (prob -> p).size(); j++) {
            generateTreeHelper(prob, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, i, j, N, info, xtree, ytree);
        }
    }
    return std::make_pair(xtree, ytree);
}

//Feed a string into a tree and put it in every bucket along the way to the leaves.
void feedString(istring *istr, std::string str, tnode *tree, bool isX, std::vector<int> *perm) {
    tnode *curr = tree;
    int i = 0;
    while(curr != NULL) {
        std::vector<bucket*> buckets = curr -> bvec;
        for(auto j = buckets.begin(); j != buckets.end(); ++j) {
            if(isX) {
                ((*j) -> xmatches).push_back(istr);
                totalX++;
            }
            else {
                ((*j) -> ymatches).push_back(istr);
                totalY++;
            }
        }
        int nextInd = std::stoi(str.substr((*perm).at(i), 1));
        curr = (curr -> children).at(nextInd);
        i++;
    }
}

//Feed every string into a tree
void feedStrings(std::vector<istring*> xstrings, std::vector<istring*> ystrings, tnode *xtree, tnode *ytree, std::vector<int> *perm) {
    for(auto i = xstrings.begin(); i != xstrings.end(); ++i) {
        feedString(*i, (*i) -> str, xtree, true, perm);
    }
    for(auto i = ystrings.begin(); i != ystrings.end(); ++i) {
        feedString(*i, (*i) -> str, ytree, false, perm);
    }
}

//Analyze the number of true and false positives in a single bucket
std::pair<long long, long long> analyzeBucket(bucket *b) {
    std::vector<istring*> xs = b -> xmatches;
    std::vector<istring*> ys = b -> ymatches;
    long long TP = 0;
    long long FP = 0;
    
    for(auto i = xs.begin(); i != xs.end(); ++i) {
        istring *x = *i;
        for(auto j = ys.begin(); j != ys.end(); ++j) {
            istring *y = *j;
            if(x -> id == y -> id) {
                if(!found.at(x -> id)) {
                    unique++;
                    found.at(x -> id) = true;
                }
                TP++;
            }
            else {
                if(!ufp.at(x -> id).at(y -> id)) {
                    funique++;
                    ufp.at(x -> id).at(y -> id) = true;
                }
                FP++;
            }
        }
    }
    return std::make_pair(TP, FP);
}

//Analyze all the buckets in a tree (which is all the buckets period).
std::pair<long long, long long> analyzeTree(tnode *tree) {
    if(tree == NULL) {
        return std::make_pair(0, 0);
    }
    long long TP = 0;
    long long FP = 0;
    std::vector<bucket*> buckets = tree -> bvec;
    for(auto i = buckets.begin(); i != buckets.end(); ++i) {
        std::pair<long long, long long> binfo = analyzeBucket(*i);
        TP += binfo.first;
        FP += binfo.second;
    }
    for(int i = 0; i < (tree -> children).size(); i++) {
        std::pair<long long, long long> info = analyzeTree((tree -> children).at(i));
        TP += info.first;
        FP += info.second;
    }
    return std::make_pair(TP, FP);
}

//Clear the xmatches and ymatches from every bucket to reset for a new iteration
void clearBuckets(tnode *tree) {
    if(tree == NULL) {
        return;
    }
    std::vector<bucket*> buckets = tree -> bvec;
    for(auto i = buckets.begin(); i != buckets.end(); ++i) {
        ((*i) -> xmatches).clear();
        ((*i) -> ymatches).clear();
    }
    for(int i = 0; i < (tree -> children).size(); i++) {
        clearBuckets((tree -> children).at(i));
    }
}

void freeTree(tnode* tree, bool freeBuckets) {
    if(tree == NULL) {
        return;
    }
    if(freeBuckets) {
        std::vector<bucket*> bux = tree -> bvec;
        for(int i = 0; i < bux.size(); i++) {
            delete bux.at(i);
        }
    }
    std::vector<tnode*> children = tree -> children;
    for(int i = 0; i < children.size(); i++) {
        freeTree(children.at(i), freeBuckets);
    }
    delete tree;
}

double runTest(probs *prob, int N, std::vector<istring*> xs, std::vector<istring*> ys, std::vector<long double> info) {
    TTP = 0;
    TFP = 0;
    deepest = 0;
    accepts = 0;
    rejects = 0;
    gx = 0.0;
    gy = 0.0;
    numNodes = 0;
    xnodes = 0;
    ynodes = 0;
    totalX = 0;
    totalY = 0;
    
    auto cstart = Clock::now();
    std::pair<tnode*, tnode*> trees = generateTree(prob, N, info);
    auto cend = Clock::now();
    
    long long treeGen = std::chrono::duration_cast<std::chrono::milliseconds>(cend-cstart).count();
    std::cout << "deepest: " << deepest << "\n";
    
    tnode *xtree = trees.first;
    tnode *ytree = trees.second;
    
    double tb = log(0.01)/log(1 - TTP);
    
    long long insert = 0;
    
    if(TTP == 0) {
        std::cout << p1 << "," << p2 << "," << p3 << "," << p4 << ",failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed\n";
        freeTree(xtree, true);
        freeTree(ytree, false);
        return -1;
    }
    
    double b = 0.0;
    
    int strl = (int)(xs.at(0) -> str).length();
    
    while(unique < 0.9 * xs.size()) {
        cstart = Clock::now();
        std::vector<int> *perm = new std::vector<int>();
        *perm = get_permut(strl, 1234 + b * 2345);
        
        feedStrings(xs, ys, xtree, ytree, perm);
        cend = Clock::now();
        insert += std::chrono::duration_cast<std::chrono::milliseconds>(cend-cstart).count();
        cstart = Clock::now();
        std::pair<long long, long long> info = analyzeTree(xtree);
        cend = Clock::now();
        delete perm;
        b++;
        clearBuckets(xtree);
        std::cout << "b: " << b << " found: " << unique << "\n";
    }
    
    double positives = unique + funique;
    std::cout << p1 << "," << p2 << "," << p3 << "," << p4 << "," << treeGen + insert + 0.015 * positives << "," << insert << "," << treeGen << "," << 0.015 * positives << "," << b << "," << unique << "," << 1 - pow(1 - (unique/N), 1/b) << "," << TTP << "," << funique << "," << 1 - pow(1 - (funique/(N * (N - 1))), 1/b) << "," << TFP << "," << accepts << "," << numNodes << "," << xnodes << "," << ynodes << "," << gx << "," << gy << "," << totalX << "," << totalY << "\n";
    freeTree(xtree, true);
    freeTree(ytree, false);
    for(int i = 0; i < found.size(); i++) {
        found.at(i) = false;
    }
    for(int i = 0; i < ufp.size(); i++) {
        for(int j = 0; j < ufp.size(); j++) {
            ufp.at(i).at(j) = false;
        }
    }
    unique = 0;
    funique = 0;
    return treeGen + insert + 0.015 * positives;
}

std::string ionToString(std::vector<std::pair<int, std::string>> strInfo) {
    std::string str = "";
    for(int i = 0; i < 2000; i++) {
        str += "3";
    }
    for(int j = 0; j < strInfo.size(); j++) {
        str.replace(strInfo.at(j).first, 1, strInfo.at(j).second);
    }
    return str;
}

void realData(probs *prob, std::vector<long double> info, std::string file) {
    std::string line;
    std::ifstream data (file);
    int id = 0;
    bool isX = true;
    std::vector<istring*> xstrings, ystrings;
    if(data.is_open()) {
        while(getline (data, line) ) {
            if(line == "BEGIN IONS") {
                std::vector<std::pair<int, std::string>> strInfo;
                while(getline (data, line)) {
                    if(line == "END IONS") {
                        std::string entry = ionToString(strInfo);
                        if(isX) {
                            istring *x = new istring();
                            x -> str = entry;
                            x -> id = id;
                            xstrings.push_back(x);
                            isX = false;
                        }
                        else {
                            double pval = matchProbability(prob, xstrings.at(id) -> str, entry);
                            double cut = 34.3749;
                            double qval = matchProbabilityQ(prob, xstrings.at(id) -> str, entry);
                            double val = pval / qval;
                            if(isnan(val) || val < cut) {
                                xstrings.pop_back();
                            }
                            else {
                                istring *y = new istring();
                                y -> str = entry;
                                y -> id = id;
                                ystrings.push_back(y);
                                id++;
                            }
                            isX = true;
                        }
                        break;
                    }
                    int index = (int)(stod(line.substr(0, line.find("\t"))) + 0.5);
                    std::string value = (line.substr(line.length() - 1, 1));
                    strInfo.push_back(std::make_pair(index, value));
                }
                
            }
        }
        data.close();
        std::cout << "Done reading data\n";
        std::cout << xstrings.size() << "\n";
        std::cout << ystrings.size() << "\n";
        
        std::vector<double> mults = {1.0/16, 1.0/8, 1.0/4, 1.0/2, 1, 2, 4};
        
        for(int i = 0; i < xstrings.size(); i++) {
            found.push_back(false);
        }
        for(int i = 0; i < xstrings.size(); i++) {
            std::vector<bool> row(xstrings.size(), false);
            ufp.push_back(row);
        }
        
        p1 = 0.125;
        p2 = 2;
        p3 = 2;
        double candidate = runTest(prob, (int)xstrings.size(), xstrings, ystrings, info);
        std::cout << "Time: " << candidate << "\n";
    }
    else {
        std::cout << "Unable to open file\n";
    }
}

int main(int argc, const char * argv[]) {
    larr pmatrix;
    pmatrix.push_back({0.000125, 0.00005, 0.000000097, 0.000405});
    pmatrix.push_back({0.00005, 0.00021, 0.0000062, 0.002});
    pmatrix.push_back({0.000000097, 0.0000062, 0.000027, 0.000355});
    pmatrix.push_back({0.000405, 0.002, 0.000355, 0.994165416});
     
    probs *prob = set_pq_values(pmatrix);
    
    std::vector<long double> info = {1.0390874586281873, 1.1226949489947105, 0.7779293468903407, 1.3263327592227026};
    
    realData(prob, info, "/file/path/here");
    
    
    return 0;
}
