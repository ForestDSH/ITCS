//
//  simulateddata.cpp
//  DSH
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
#include <algorithm>
#include <string.h>

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

//2D vector that holds doubles
typedef std::vector<std::vector<double>> arr;

//p and q are 2D vectors that represent a probability matrix
struct probs_header {
    arr p, q;
    std::vector<double> px, py, qx, qy;
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
//Xcode linker was not functioning
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

//Converted from make_data in common_funcs.cpp to work with any size language
std::pair<std::vector<istring*>, std::vector<istring*>> make_data(probs *P, int N, int T) {
    std::vector<istring*> X;
    std::vector<istring*> Y;
    int s = (int)(P -> qx).size();
    
    for (int i = 0; i < N; i++) {
        
        istring *x = new istring();
        x -> id = i;
        x -> str = "";
        istring *y = new istring();
        y -> id = i;
        y -> str = "";
        for (int j = 0; j < T; j++) {
            int rand_num = my_rand(&init_seed) % MODULO;
            int xval = 0;
            int accum = (P -> px).at(0) * MODULO;
            while(accum < rand_num) {
                xval++;
                accum += (P -> px).at(xval) * MODULO;
            }
            rand_num = my_rand(&init_seed) % MODULO;
            int yval = 0;
            accum = (P -> p).at(xval).at(0) / (P -> px).at(xval) * MODULO;
            while(accum < rand_num) {
                yval++;
                accum += (P -> p).at(xval).at(yval) / (P -> px).at(xval) * MODULO;
            }
            x -> str += std::to_string(xval);
            y -> str += std::to_string(yval);
        }
        
        X.push_back(x);
        Y.push_back(y);
    }
    
    return make_pair(X, Y);
}

//Compute the q matrix given the p matrix and set up a probability distribution with them
probs* set_pq_values(arr pmatrix) {
    
    probs *ret = new probs();
    arr qmatrix;
    
    ret -> p = pmatrix;
    
    std::vector<double> rowsums(pmatrix.size(), 0.0);
    std::vector<double> colsums(pmatrix.size(), 0.0);
    
    for(int i = 0; i < pmatrix.size(); i++) {
        for(int j = 0; j < pmatrix.size(); j++) {
            rowsums.at(i) += pmatrix.at(i).at(j);
            colsums.at(j) += pmatrix.at(i).at(j);
        }
    }
    
    ret -> px = rowsums;
    ret -> py = colsums;
    
    for(int i = 0; i < pmatrix.size(); i++) {
        std::vector<double> newrow;
        for(int j = 0; j < pmatrix.size(); j++) {
            newrow.push_back(rowsums.at(i) * colsums.at(j));
        }
        qmatrix.push_back(newrow);
    }
    
    ret -> q = qmatrix;
    
    std::vector<double> qx(qmatrix.size(), 0.0);
    std::vector<double> qy(qmatrix.size(), 0.0);
    
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
    return P/Qx < pow(N, 1 - lstar) * p2 || P/Qy < pow(N, 1 - lstar) * p3;
}

//Given R and the corresponding P and Q values, calculate rij
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
                slope += pow((prob -> p).at(k).at(j), mu + 1) * pow((prob -> p).at(k).at(j), t) * log((prob -> q).at(k).at(j));
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

//The probability that x and y were generated given q
double matchProbabilityQ(probs *prob, std::string x, std::string y) {
    double product = 1.0;
    for(int i = 0; i < x.length(); i++) {
        int xind = std::stoi(x.substr(i, 1));
        int yind = std::stoi(y.substr(i, 1));
        product *= (prob -> q).at(xind).at(yind);
    }
    return product;
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
    return info;
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
    
    /*NEW CONTROL FLOW
      First create the xtree and ytree nodes if they haven't already been created.
      Check for accept/reject
      Recursive call if not
     */
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
            deepest = (currX -> str).length();
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

//Return true if we should prune the tree
bool pruneTree(tnode* tree) {
    if(tree == NULL) {
        return true;
    }
    bool isLeaf = true;
    for(int i = 0; i < (tree -> children).size(); i++) {
        if((tree -> children).at(i) != NULL) {
            isLeaf = false;
        }
    }
    if(isLeaf) {
        if((tree -> bvec).size() == 0) {
            xnodes--;
	    delete tree;
            return true;
        }
        return false;
    }
    else {
        bool prune = true;
        for(int i = 0; i < (tree -> children).size(); i++) {
            bool pruneChild = pruneTree((tree -> children).at(i));
            if(pruneChild) {
                (tree -> children).at(i) = NULL;
            }
            prune = prune && pruneChild;
        }
        prune = prune && ((tree -> bvec).size() == 0);
        if(prune) {
	    xnodes--;
            delete tree;
        }
        return prune;
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
                TP++;
            }
            else {
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

    tnode *xtree = trees.first;
    tnode *ytree = trees.second;
    
    double tb = log(0.01)/log(1 - TTP);
    
    long long insert = 0;
    
    long long positives = 0;
    
    if(TTP == 0) {
        std::cout << p1 << "," << p2 << "," << p3 << ",failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed,failed\n";
        freeTree(xtree, true);
        freeTree(ytree, false);
        return -1;
    }

    pruneTree(xtree);
    pruneTree(ytree);
    
    double b = 0.0;
    
    double tprate = 1.0;
    
    int strl = (xs.at(0) -> str).length();
    double ETP = 0.0;
    double EFP = 0.0;

    while(tprate > 0.01) {
        cstart = Clock::now();
        std::vector<int> *perm = new std::vector<int>();
        *perm = get_permut(strl, 1234 + b * 2345);
        feedStrings(xs, ys, xtree, ytree, perm);
        cend = Clock::now();
        insert += std::chrono::duration_cast<std::chrono::milliseconds>(cend-cstart).count();
        
        //The false positive penalty is being approximated with 0.015 * #positives, so this time taken for this part is not actually used anywhere
        cstart = Clock::now();
        std::pair<long long, long long> info = analyzeTree(xtree);
        cend = Clock::now();
        
        long long TP = info.first;
        long long FP = info.second;
        positives += TP + FP;
        ETP += TP;
        EFP += FP;
        tprate *= 1.0 - ((double)TP/(double)N);
        
        delete perm;
        b++;
        clearBuckets(xtree);
    }
    std::cout << p1 << "," << p2 << "," << p3 << "," << treeGen + insert + 0.015 * positives << "," << insert << "," << treeGen << "," << 0.015 * positives << "," << b << "," << ETP << "," << 1 - pow(tprate, 1/b) << "," << TTP << "," << EFP << "," << EFP/(b * N * N) << "," << TFP << "," << accepts << "," << numNodes << "," << xnodes << "," << ynodes << "," << gx << "," << gy << "," << totalX << "," << totalY << "\n";
    freeTree(xtree, true);
    freeTree(ytree, false);
    return treeGen + insert + 0.015 * positives;
}

int main(int argc, const char * argv[]) {
    if(argc < 7 || argc > 8) {
        std::cout << "usage: ./simulated <N> <S> <C1> <C2> <C3> <matrix> <data>\n";
        return -1;
    }
    
    int N = atoi(argv[1]);
    int S = atoi(argv[2]);
    p1 = atof(argv[3]);
    p2 = atof(argv[4]);
    p3 = atof(argv[5]);
    std::string matrix = argv[6];
    std::ifstream file(matrix);
    arr p;
    const int MAXLINE = 256;
    char line[MAXLINE];
    char delim[] = ",";
    char *token;
    while(file) {
        std::vector<double> newRow;
        file.getline(line, MAXLINE);
        if(line[0] == '\0') {
            break;
        }
        token = strtok(line, delim);
        newRow.push_back(atof(token));
        while((token = strtok(NULL, delim)) != NULL) {
            newRow.push_back(atof(token));
        }
        p.push_back(newRow);
    }
    


    auto pstart = Clock::now();
    
    
    probs *prob = set_pq_values(p);
    std::vector<long double> info = geometricLambda(prob);
    std::pair<std::vector<istring*>, std::vector<istring*>> strs;
    if(argc == 7) {
	strs = make_data(prob, N, S);
    }
    else {
	std::string d = argv[7];
	std::ifstream data(d);
	int count = 0;
	std::vector<istring*> xstrs, ystrs;
	const int MAXDATA = 2 * S + 2;
	char dline[MAXDATA];
	char *dtoken;
	while(data) {
	    data.getline(dline, MAXDATA);
	    if(dline[0] == '\0') {
		break;
	    }
	    dtoken = strtok(dline, delim);
	    istring *x = new istring();
	    x -> str = dtoken;
	    x -> id = count;
	    xstrs.push_back(x);
	    dtoken = strtok(NULL, delim);
	    istring *y = new istring();
	    y -> str = dtoken;
	    y -> id = count;
	    ystrs.push_back(y);
	    count++;
	}
	std::cout << count << "\n";
	strs = std::make_pair(xstrs, ystrs);
    }
    std::vector<istring*> xs = strs.first;
    std::vector<istring*> ys = strs.second;
    std::cout << "C1,C2,C3,Total complexity,Complexity of hashing,Complexity of tree construction,Complexity of FP,#bands needed,Overall empirical TP,TP at one band,Theoretical TP in one band,Overall empirical FP, empirical FP in one band,Theoretical FP in one band,#buckets,#nodes in the tree,total number of x nodes,total number of y nodes,gamma_x,gamma_y,mapped_x,mapped_y\n";
    double candidate = runTest(prob, N, xs, ys, info);
    auto pend = Clock::now();
    std::cout << "Total run time: " << std::chrono::duration_cast<std::chrono::milliseconds>(pend-pstart).count() << "\n";
    return 0;
}
