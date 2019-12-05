from sage.homology.homology_group import HomologyGroup

#========================
#Schubertcell class
#========================
class Schubertcell:
        
    def __init__(self, osp):
        #the osp as a permutation
        self.id = Permutation(osp);
        #dim of cell (since minimal representative, equals length)
        self.dim = self.id.length();
        #dictionary of inneighbors via d. keys: Permutation(), vals: ``neighbor'', see below
        self.inneighbors = {};
        #dictionary of outneighbors via d. keys: Permutation(), vals: ``neighbor'', see below
        self.outneighbors = {};
        #each ``neighbor'' is a dictionary with keys 'cell', 'id', 'a', 'b', 'alpha', 'beta', 'incident', 'weight'
        
        #dictionary of index of element in permutation
        self.elementindex = {};                                                                
        for i in osp:
            self.elementindex[i] = osp.index(i);
    #return osp[i]    
    def __getitem__(self, arg):
        if arg in ZZ:
            return self.id[arg];
        
    #===========
    #GET METHODS    
    #===========
    #return index of element a in permutation (i.e. inverse)
    def get_index(self, a):
        return self.elementindex[a];
    
    #return GI(a,alpha,beta) as defined in paper
    def get_GI(self, a, Ia, alpha, beta):
        k = self.get_index(a)
        left = alpha - Ia;
        right = beta - Ia;
        return self.GI[left][k]-self.GI[right][k];
    
    #return LI(a,alpha,beta) as defined in paper
    def get_LI(self, a, Ia, alpha,beta):
        k = self.get_index(a)
        left = alpha - Ia;
        right = beta - Ia;
        return self.LI[left][k]-self.LI[right][k];
        
    #===========
    #SET METHODS
    #===========
    #GI[j][k]: the number of elements greater than I[k], to the right of k, at least j blocks away
    #LI[j][k]: the number of elements smaller than I[k], to the right of k, at least j blocks away
    def initialize_GILI(self, GI, LI):                     
        self.GI = GI;
        self.LI = LI;                                                                
    
    #sth element in dimension d (d=dim of Schubertcell)
    def set_s(s):
        self.s = s;
    
    #inneighbor: Schubert cell, a>b, a in I(alpha), b in I(beta)
    def add_inneighbor(self, inneighbor, a, b, alpha, beta):
        self.inneighbors[inneighbor.id] = {'cell' : inneighbor, 'id' : inneighbor.id, 'a' : a, 'b' : b, 'alpha' : alpha, 'beta' : beta};

    #outneighbor: Schubert cell, a>b, a in I(alpha), b in I(beta)        
    def add_outneighbor(self, outneighbor, a, b, alpha, beta):
        self.outneighbors[outneighbor.id] = {'cell' : outneighbor, 'id' : outneighbor.id, 'a' : a, 'b' : b, 'alpha' : alpha, 'beta' : beta};
        

#========================
#flagcomplex class
#========================
class flagcomplex:
    def __init__(self, D, computecohomology = True, verbose = False, writetofile = False):        
     
        #===============================================
        #create parameters with same names as in paper
        #===============================================
        #D: the differences in dimensions in Fl_D
        self.D = D;
        #S: the dimensions in Fl_D, should start by 0 for indexing
        S = [0];                                                        
        S.extend([sum(D[:i+1]) for i in range(len(D))]);
        #m: the number of subspaces in Fl_D
        m = len(D);
        #N: the total dimension in Fl_D
        N = sum(D);
        #Q: the dimensions of the quotient subspaces
        Q = [N-S[i] for i in range(1,m+1)]
        #dim: dim(Fl_D) as manifold
        dim = sum([D[i]*Q[i] for i in range(0,m)])
        #nextblock: for position i, nextblock[i] is the starting position of the next block in osp
        nextblock = {};
        #blockid[i] returns the number of the block in which position i falls
        blockid = {}
        
        j = 1;
        
        for i in range(N):
            if i >= S[j]:
                j = j+1;
            nextblock[i] = S[j];
            blockid[i] = j-1;    
        
        #===========================================================================================
        #generate vertices/Schubertcells recursively as dictionary indexed by ordered set partitions
        #===========================================================================================
        #vertices[c] contains Schubert cells of codimension c        
        vertices = {};
        #codimdictionary[c][s] is the sth Schubert cell of codim c
        codimdictionary = {};
        
        for c in range(dim+1):
            codimdictionary[c] = {};
            
        #input: D sized boxes, A of size sum D, initial segment already in boxes
        def OSPgen(D, A, initial):
            S = Subsets(len(A), D[0]);                                        
            #for all D[0] element subsets I of len(A)
            for i in range(len(S)):
                B = [];
                Isorted = sorted(S[i]);
                A0 = list(A);
                for j in range(D[0]):                           #output B (initial) and A0 (remainder)
                    B.append(A[Isorted[j]-1]);                  #fill B with the Ith elements of A
                for j in range(D[0]-1, -1,-1):
                    del A0[Isorted[j]-1];
                initial0 = list(initial + B);
                if len(D)>2:
                    OSPgen(D[1:], A0, initial0)
                if len(D)==2:
                    new = Schubertcell(initial0 + A0)           #create Schubert cell
                    p = Permutation(initial0 + A0);
                    vertices[p] = new;                          #set vertex to Schubert cell
                    codim = dim-new.dim;                        #set codimension
                    s = len(codimdictionary[codim]);
                    codimdictionary[codim][s] = new;            #add to dictionary
                    new.s = s;
            return;
        
        
        OSPgen(D, range(1, N+1), [])
        if verbose:
            print 'vertices done'
            
            
        #======================================================================================================
        #for each osp I (a permutation object!), compute GI[j][k] (LI[j][k]):  
        #the number of elements that are greater (smaller) than I[k], to the right of k, at least j blocks away
        #======================================================================================================                
        for I in vertices:
            GI = {};
            GI[m-1] = [0]*N;
            LI = {};
            LI[m-1] = [0]*N;
            #to the right
            for j in range(1,m):                                                #for each block-distance
                GI[m-j-1] = [GI[m-j][o] for o in range(N)];
                LI[m-j-1] = [LI[m-j][o] for o in range(N)];
                for k in range(S[j]):                                           #for all elements in first j blocks
                    for l in range(S[blockid[k]+m-j],S[blockid[k]+m-j+1]):      #for all elements in the new block (by increasing j)
                        if I[l] > I[k] and l > k:
                            GI[m-1-j][k] += 1;
                        if I[l] < I[k] and l > k:
                            LI[m-1-j][k] += 1;
            #to the left
            for j in range(m):                                                  #for each block-distance
                GI[-j-1] = [GI[-j][o] for o in range(N)];
                LI[-j-1] = [LI[-j][o] for o in range(N)];
                for k in range(S[j],S[m]):                                      #for all elements in last m-j blocks
                    for l in range(S[blockid[k]-j],S[blockid[k]-j+1]):          #for all elements in the new block (by increasing j)
                        if I[l] > I[k]:
                            GI[-j-1][k] += 1;
                        if I[l] < I[k]:
                            LI[-j-1][k] += 1;    
            vertices[I].initialize_GILI(GI,LI);
        if verbose:
            print 'GILI done'
        
        #===============================================
        #generate graph of Schubert cells indexed by osp
        #===============================================
        for v in vertices.values():
            #all bruhat successors, which are arbitrary permutations
            for neighborid in v.id.bruhat_succ():
                #save, if it is an OSP (minimal in its coset)
                if neighborid in vertices:

                    transposition = v.id.right_action_product(neighborid.inverse()).cycle_tuples(false)[0];

                    a = neighborid[transposition[0]-1];
                    b = neighborid[transposition[1]-1];

                    alpha = blockid[transposition[0]-1];                        #index alpha of block
                    beta = blockid[transposition[1]-1];                         #index beta of block

                    v.add_inneighbor(vertices[neighborid], a, b, alpha, beta)
                    vertices[neighborid].add_outneighbor(v, a, b, alpha, beta)
        if verbose:
            print 'edges done'
        
        
        #======================================================
        #incident: true if 0, false if +-2 
        #======================================================
        for vertex in vertices.values():
            for neighbor in vertex.outneighbors.values():
                cell, id, a, b, alpha, beta = neighbor['cell'], neighbor['id'], neighbor['a'], neighbor['b'], neighbor['alpha'], neighbor['beta']
                GI = vertex.get_GI(a, alpha, alpha, beta);
                LI = vertex.get_LI(b, beta, alpha-1, beta-1);
                
                neighbor['incident'] = not is_even(GI+LI);
                cell.inneighbors[vertex.id]['incident'] = not is_even(GI+LI);
        if verbose:
            print 'incidences done'


        self.S = S
        self.m = m;
        self.N = N;
        self.Q = Q;
        self.dim = dim;
        self.nextblock = nextblock;
        self.blockid = blockid;
        self.vertices = vertices;
        self.codimdictionary = codimdictionary;
        
        if computecohomology:
            self.compute_incidencematrices(verbose);
            self.compute_cohomology(verbose);
            self.print_generators(writetofile);
    
    #for a list p, return Schubert cell vertices[p]
    def __call__(self, p):
        return self.vertices[Permutation(p)];
    
    #return cells of codim c
    def get_codimcells(self,c):
        return [x.id for x in self.codimdictionary[c].values()]
        
    def compute_incidencematrices(self, verbose = False):
        codimdictionary = self.codimdictionary;
        m = self.m - 1;                         #-1, since m is a length, and indexing starts from 0...
        N = self.N;
        dim = self.dim;
        blockid = self.blockid;
        
        incidencematrices = [matrix(len(codimdictionary[c]),len(codimdictionary[c+1])) for c in range(dim)]
        self.incidencematrices = incidencematrices;
        
        for v in self.vertices.values():
            for n in v.outneighbors.values():
                if n['incident']:
                    neighbor, id, a, b, alpha, beta = n['cell'], n['id'], n['a'], n['b'], n['alpha'], n['beta']                
                    #==========================
                    #FIRST TERM:c1 
                    #=========================
                    c1 = v.get_GI(b,beta,alpha,m) - v.get_GI(a,alpha,alpha,m);
                    
                    for i in range(1,b):
                        posi = v.get_index(i);
                        iota = blockid[posi];
                        c1 += v.get_GI(i,iota,iota,m);
                        
                    #=================================
                    #SECOND TERM: c2
                    #=================================
                    c2 = v.get_GI(a,alpha,alpha,m)-v.get_GI(a,alpha,beta,m)
                    t2 = v.get_GI(a,alpha,beta,m);
                    for i in range(b+1,a):
                        posi = v.get_index(i);
                        iota = blockid[posi];
                        t2 += v.get_GI(i,iota,iota,m);
                    c2 *= t2;
                    
                    #==========================
                    #THIRD TERM:c3
                    #========================== 
                    c3 = 0;
                    for i in range(1,b):
                        posi = v.get_index(i);
                        iota = blockid[posi];
                        if alpha<= iota < beta:
                            c3 += v.get_GI(b, beta, iota, m) - v.get_GI(a, alpha, iota, m)    
                    
                    #========================================
                    #FOURTH TERM: c4
                    #========================================
                    c4 = v.get_LI(b, beta, alpha-1, beta-1) + 1;
                    
                    #========================================
                    #COMPUTE SIGN
                    #========================================                    
                    
                    sign = c1 + c2 + c3 + c4;
                    #print c1, c2, c3, c4, v.id, id
                    incidencematrices[dim - v.dim][v.s,neighbor.s] = (-1)^sign * 2;
                    n['weight'] = (-1)^sign * 2;
                
        self.incidencematrices = incidencematrices;
        if verbose:
            print 'incidencematrices done'
        
    
    def compute_cohomology(self, verbose = False):
        dim = self.dim;
        incidencematrices = [x.transpose() for x in self.incidencematrices];
        Z = HomologyGroup(1, ZZ);
        C2 = HomologyGroup(1, ZZ, [2]);
        twotorsion = True;
        chain = ChainComplex(incidencematrices);

        generators = [];                                        #generators[c][i] for c codim is == (G, Chain:(c:coeffs)), 
                                                                #G is the group generated by the coeffs in a +-1 vector
        Zgenerators = [[] for i in range(dim+1)];               #Zgenerators[c][i] for c codim is == Chain:(c:coeffs)
        Zgeneratorsasvector = [[] for i in range(dim+1)];       #Zgeneratorsasvector[c][i] is the coeffs vector (1 0 0 -1 ...)
        Zgeneratorcells = [[] for i in range(dim+1)];           #Zgeneratorcells[c][j] is a list of OSPs whose signed sum is the jth generator of codim c
        
        for c in range(dim+1):                                  #for each codimension
            if verbose:
                print c;
            generators.append(chain.homology(deg = c, generators = true));
            for generator in generators[c]:
                if generator[0] == Z:
                    Zgenerators[c].append(generator[1]);        #generators[i][j][1], [1] corresponds to the Chain part
                elif generator[0] != C2:
                    twotorsion = False;
        self.generators, self.Zgenerators = generators, Zgenerators;
         
        if twotorsion:
            print "Cohomology has only 2-torsion."
        else:    
            print "COHOMOLOGY HAS NOT ONLY 2-TORSION!"
            
        for c in range(dim+1):                                  #for each codimension        
            for Zgenerator in Zgenerators[c]:                   #for each Z summand
                generatorvector = Zgenerator.vector(c);         #generator as a vector of indices
                Zgeneratorsasvector[c].append(generatorvector); #save 
                Zgeneratorcells[c].append([]);                  #create a list of Schubert cells
                for s in range(len(generatorvector)):    
                    if generatorvector[s] != 0:                 #if it appears with nonzero coefficient, add to the list
                        Zgeneratorcells[c][-1].append(self.codimdictionary[c][s].id); 
        
        self.Zgeneratorsasvector, self.Zgeneratorcells = Zgeneratorsasvector, Zgeneratorcells;

    #Writes to file, also prints generators.
    def print_generators(self, writetofile = False):
        D, dim, Zgeneratorcells = self.D, self.dim, self.Zgeneratorcells;
        
        filename = 'cohomology';
        for i in range(len(D)):
            filename = filename + str(D[i]);
        filename = filename + '.txt';
        if writetofile:
            outputfile = open(filename, 'w')
        for c in range(dim+1):
            for gen in Zgeneratorcells[c]:
                s='';
                for k in range(len(gen)):
                    if k > 0:                                   #if not first element, formatting
                        s += ', ';
                    s += str(gen[k]);
                outputstring = 'codim ' + str(c) + ': ' + s + "\r\n\r"; 
                print outputstring
                if writetofile:
                    outputfile.write(outputstring)
        if writetofile:
            outputfile.close()			
#

