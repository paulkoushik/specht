####Section-1. The group, generators and class reps


#Monomial group generators as matrices in GL_n(C) with r-th roots of unity
MonoGens:= function(n, r)
local gen, l, i;
    gen:= [];
    l:= ListWithIdenticalEntries(n, 1);
    l[1]:= E(r);
    Add(gen, DiagonalMat(l));
    for i in [1..(n-1)] do
        Add(gen, PermutationMat((i, i+1), n, 1));
    od;
return gen;
end;

#Monomial Group
MonoGroup:= function(n, r)
local gens;
    gens:= MonoGens(n, r);
return GroupWithGenerators(gens);
end;

#Class representatives as a block matrix
MonoRep:= function(lambda)
local n, M, o, i, a, mat, r;
n:= Sum(lambda, Sum);
r:= Length(lambda);
M:= NullMat(n,n);
o:= 0;
for i in [1..r] do
    for a in lambda[i] do
        mat:= PermutationMat(PermList(([1..a] mod a) + 1), a);
        mat[a][1]:= E(r)^(i-1);
        M{o+[1..a]}{o+[1..a]}:= mat;
        o:= o + a;
    od;
od;
return M;
end;



####Section-2. Partitions and words



#Multipartitions of a number n having r partitions
MultiPartitions:= function(n, r)
return PartitionTuples(n, r);
end;

#Conjugate multipartition
ConjugateMultiPartition:= function(lambda)
return List(lambda, AssociatedPartition);
end;

#Word corresponding to a multipartition
WordMultiPartition:= function(multipartition)
local WordPartition, W, u, l, i, j;

    WordPartition:= function(lambda)
    local i, l, u;
        u:= [];
        for l in [1..Length(lambda)] do
            for i in [1..lambda[l]] do
                Add(u, l);
            od;
        od;
    return u;
    end;

    W:= [];
    l:= List(multipartition, WordPartition);
    for i in [1..Length(multipartition)] do
        for j in l[i] do
            Add(W, [j, i-1]);
        od;
    od;
return W;
end;


#Multipartition corresponding to a word
MultiPartitionWord:= function(word)
local lambda, index, l, i;
    index:= Set(List(word, l -> l[2]));
    lambda:= List(index, i -> []);
    for i in Set(word) do
        Add(lambda[i[2]], Size(Positions(word, i)));
    od;
return lambda;
end;



#####Section-3. Multitableaux and pairs of words



#Standard Young multitableaux (SYMTs) for a multipartition lambda
SYMTs:= function(multipartition)
local   isOneHook,  removeOneHook,  addOneHook,  n,  list,  i, k, lambda,
        new,  t;
#here lambda is an ordinary partition
    isOneHook:= function(lambda, i)
        return i = Length(lambda) or lambda[i] > lambda[i+1];
    end;

    removeOneHook:= function(multipartition, k, i)
        local lambda, new;
        lambda:= ShallowCopy(multipartition[k]);
        new:= ShallowCopy(multipartition);
        if i = Length(lambda) and lambda[i] = 1 then
            new[k]:= lambda{[1..i-1]};
        else
            lambda[i]:= lambda[i]-1;
            new[k]:= lambda;
        fi;
        return new;
    end;

    addOneHook:= function(t, k, i, n)
        if i > Length(t[k]) then
            Add(t[k], [n]);
        else
            Add(t[k][i], n);
        fi;
        return t;
    end;

    # trivial case first
    if ForAll(multipartition, x -> x = []) then
        return [List(multipartition, x -> [[]])];
    fi;

    # initialize
    n:= Sum(multipartition, Sum);
    list:= [];

    # loop
    for k in Reversed([1..Length(multipartition)]) do 
        lambda:= multipartition[k];
        for i in Reversed([1..Length(lambda)]) do
            if isOneHook(lambda, i) then
                new:= removeOneHook(multipartition, k, i);
                for t in SYMTs(new) do
                    addOneHook(t, k, i, n);
                    Add(list, t);
                od;
            fi;
        od;
    od;

    return list;
end;

#Canonnical multitableau for a multipartition lambda
CanonicalMultiTableau:= function(lambda)
local CanonicalTableau, tab, i;
    CanonicalTableau:= function(lambda)
    local t, o, l;
        t:= [];
        o:= 0;
            for l in lambda do
                Add(t, o + [1..l]);
                o:= o + l;
            od;
        return t;
    end;
    tab:= List(lambda, CanonicalTableau);
    for i in [2..Length(lambda)] do
        if lambda[i] <> [] then
            tab[i]:= tab[i] + Sum(List(lambda{[1..i-1]}, Sum));
        fi;
    od;
return tab;
end;

#Word corresponding to a multitableau
WordsMultiTableau:= function(tab)
local rows, cols, i, j, k, a;
    rows:= [];
    cols:= [];
    for i in tab do
        for j in [1..Length(i)] do
            for k in [1..Length(i[j])] do
                a:= i[j][k];
                rows[a]:= [j, Position(tab, i)-1];
                cols[a]:= [k, Position(tab, i)-1];
            od;
        od;
    od;
return [rows, cols];
end;



####Section4. Specht object


#Young character of two words u and v
YoungCharMono:= function(u, v)
local c, d, pi, i;
    c:= TransposedMat([u,v]);
    if Size(Set(c)) < Length(c) then
        return 0;
    fi;
    for i in c do
        if i[1][2] <> i[2][2] then
            return 0;
        fi;
    od;
    
    d:= ShallowCopy(c);
    pi:= Sortex(d);
    
    return SignPerm(pi);
end;

#Specht matrix corresponding to the arrangements of the row word and column words A and B respectively
SpechtMatMono:= function(A1, A2)
    local u, v, matrix, row;
    matrix:= [];
        for u in A1 do
            row:= [];
                for v in A2 do
                    Add(row, YoungCharMono(u,v));
                od;
            Add(matrix, row);
        od;
return matrix;
end;

#Specht object to record all the previous information needed for further concepts
SpechtMono:= function(lambda)
    local n, w1, w1reversed, w2reversed, w2, A, sigma, B, sm, symt, words, k;

    n:= Sum(lambda, Sum);
    w1:= WordMultiPartition(lambda);
    
    #sorting the words lexicographically in the set of all arrangements of w1
    
    w1reversed:= List(Arrangements(List(w1, Reversed), Length(w1)));
    A:= List(w1reversed, w -> List(w, Reversed));
    
    #ind:= List(A, i -> List(i, j -> j[2]));
    #pi:= Sortex(ind);
    #A1:= Permuted(A, pi);

    sigma:= ConjugateMultiPartition(lambda);
    w2:= WordMultiPartition(sigma);
    
    #sorting the words lexicographically in the set of all arrangements of w2
    
    w2reversed:= List(Arrangements(List(w2, Reversed), Length(w2)));
    B:= List(w2reversed, w -> List(w, Reversed));

    sm:= SpechtMatMono(A, B);
    #sm:= SpechtMatCRG(A1, B);
    
    symt:= SYMTs(lambda);

    words:= List(symt, WordsMultiTableau);
    k:= List(words, i -> [Position(A, i[1]), Position(B, i[2])]);
    #k:= List(words, i -> [Position(A1, i[1]), Position(B, i[2])]);

   return rec(sm:= sm, A:= A, B:= B, k:= k, symt:= symt);
end;



####Section-5. Representing matrices


###Representing matrix corresponding to a matrix element in the monomial group is a product of two matrices, a diagonal matrix and a permutation matrix


#The diagonal matrix D corresponding to the decomposition of the rep mat of an elemet in the group, we say that the diagonal is consisted of the signs
SpechtRepSign:= function(specht, mat)
local n, so, l, sign, index, D;

    n:= Length(mat);
    l:= List(specht.k, i -> i[1]);
    sign:= List(mat, row -> First(row, i -> i <> 0));
    #index:= List(specht.A{l}, i -> i[1][2]);
    index:= List(specht.A{l}, i -> Product([1..n], j -> sign[j]^i[j][2]));
    D:= DiagonalMat(index);

return D;
end;


#The permutation matrix P corresponding to the decomposition of the rep mat of an elemet in the group, we say that the diagonal is consisted of the signs
SpechtRepPermMat:= function(specht, mat)
local n, sigma, pi, smT, l, submat, k, M, P;
    n:= Length(mat);
    sigma:= PermList(List(mat, x -> PositionProperty(x, i -> i <> 0)));
    pi:= Permutation(sigma, specht.A, Permuted);
    smT:= TransposedMat(specht.sm);
    l:= List(specht.k, i -> i[2]);
    submat:= smT{l};
    k:= List(submat, i -> Permuted(i, pi));
    P:= List(k, i -> SolutionMat(submat, i));
return P;
end;

#The representing matrix corresponding to a matrix element Mat in G(r,1,n) as a product of the diagonal mat D and Permutation mat P, i.e., Mat:= D*P
SpechtRepMono:= function(specht, mat)
local D, P;
    D:= SpechtRepSign(specht, mat);
    P:= SpechtRepPermMat(specht, mat);
return D*P;
end;



####Section-6. Characters and Character table


#Characters correspnding to a multipartition lambda for all the class reps
MonoCharacter:= function(lambda, reps)
local n, r, ClassReps, specht, RepMats;
    n:= Sum(lambda, Sum);
    r:= Length(lambda);
#    ClassReps:= MonoRep(lambda);
    specht:= SpechtMono(lambda);
    RepMats:= List(reps, x -> SpechtRepMono(specht, x));
    return List(RepMats, x -> Trace(x));
end;


#Character table for all the multipartitions lambda of n
MonoCharTable:= function(n, r)
local P, reps, CharTable;
    P:= MultiPartitions(n, r);
    reps:= List(P, MonoRep);
    CharTable:= List(P, lambda -> MonoCharacter(lambda, reps));
return CharTable;
end;



