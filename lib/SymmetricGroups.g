####Section-1. The group, generators and class reps


#Symmetric group generators
SymmGens:= function(n)
local gens, i;
    gens:= [];
    for i in [1..n-1] do
        Add(gens, (i, i+1));
    od;
return gens;
end;

#Symmetric Group
SymmGroup:= function(n)
local G;
    G:= GroupWithGenerators(SymmGens(n));
return G;
end;


#Class representatives 
SymmRep:= function(lambda)
local cycle, p, classes, cycle_list, cycle_structure;
    cycle_list:= [];
    
    cycle:= function(n)
        return ([1..n] mod n) + 1;
    end;

    for p in lambda do
        Append(cycle_list, cycle(p) + Length(cycle_list));
    od;

    cycle_structure:= PermList(cycle_list);
return cycle_structure;
end;



####Section-2. Partitions and words


#Conjugate partition
ConjugatePartition:= function(lambda)
return AssociatedPartition(lambda);
end;

#Word corresponding to a partition
WordPartition:= function(lambda)
local i, l, W;
W:= [];
    for l in [1..Length(lambda)] do
        for i in [1..lambda[l]] do
            Add(W, l);
        od;
    od;
return W;
end;


#Partition corresponding to a word
PartitionWord:= function(word)
local lambda, i;
    Sort(word);
    lambda:= [];
    for i in Set(word) do
        Add(lambda, Size(Positions(word, i)));
    od;
return lambda;
end;



#####Section-3. Tableaux and pairs of words



#Standard Young tableaux for a partition lambda
SYTs:= function(lambda)
local   isOneHook,  removeOneHook,  addOneHook,  n,  list,  i,  new,  t;

    isOneHook:= function(lambda, i)
        return i = Length(lambda) or lambda[i] > lambda[i+1];
    end;

    removeOneHook:= function(lambda, i)
        local new;
        if i = Length(lambda) and lambda[i] = 1 then
            return lambda{[1..i-1]};
        fi;
        new:= ShallowCopy(lambda);
        new[i]:= new[i]-1;
        return new;
    end;

    addOneHook:= function(t, i, n)
        if i > Length(t) then
            Add(t, [n]);
        else
            Add(t[i], n);
        fi;
        return t;
    end;

    # trivial case first
    if lambda = [1] then
        return [[[1]]];
    fi;

    # initialize
    n:= Sum(lambda);
    list:= [];

    # loop
    for i in Reversed([1..Length(lambda)]) do
        if isOneHook(lambda, i) then
            new:= removeOneHook(lambda, i);
            for t in SYTs(new) do
                addOneHook(t, i, n);
                Add(list, t);
            od;
        fi;
    od;

    return list;
end;


#Canonnical tableau for a partition lambda
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

#Word corresponding to a tableau
WordsTableau:= function(tableau)
local rows, cols, i, k, a;
    rows:= [];
    cols:= [];
        for i in [1..Length(tableau)] do
            for k in [1..Length(tableau[i])] do
                a:= tableau[i][k];
                rows[a]:= i;
                cols[a]:= k;
            od;
        od;
return rec(rows:= rows, cols:= cols);
end;

#Tableau corresponding to a word
TableauWords:= function(row_word, col_word)
local pair, pairTransposed, lambda, tableau, i;
    pair:= [row_word, col_word];
    pairTransposed:= TransposedMat(pair);
    lambda:= PartitionWord(row_word);
    tableau:= CanonicalTableau(lambda);
    if Size(Set(pairTransposed)) < Length(pairTransposed) then
        return false;
    else
        for i in pairTransposed do
            tableau[i[1]][i[2]]:= Position(pairTransposed, i);
        od;
    fi;
return tableau;
end;

#Transpose of a tableau corresponding to the conjugate partition
ConjugateTableau:= function(t)
local i, j, result;
result:= List(t[1], x -> []);
    for i in [1..Length(t)] do
        for j in [1..Length(t[i])] do
            result[j][i]:= t[i][j];
        od;
    od;
return result;
end;

#Intersection tableau at the intersection of two tableaux t and s
IntersectionTableau:= function(t,s)
local cols, tt, a, uu, row, i, k;
    cols:= WordsTableau(t).cols;
    uu:= List(t[1], x -> []);
        for row in s do
            for i in [1..Length(row)] do
                a:= row[i];
                k:= cols[a];
                Add(uu[k], a);
            od;
        od;
    return TransposedMat(uu);
end;



####Section4. Specht object


#Young character of two words u and v
YoungCharSymm:= function(u, v)
local c, d, pi;
    c:= TransposedMat([u,v]);
        if Size(Set(c)) < Length(c) then
            return 0;
        fi;
    d:= ShallowCopy(c);
    pi:= Sortex(d);
return SignPerm(pi);
end;

#Specht matrix corresponding to the arrangements of the row words and column word A and B respectively
SpechtMatSymm:= function(A, B)
local u, v, matrix, row;
    matrix:= [];
    for u in A do
    row:= [];
        for v in B do
            Add(row, YoungCharSymm(u,v));
        od;
        Add(matrix, row);
    od;
return matrix;
end;

#Specht object to record all the previous information needed for further concepts
SpechtSymm:= function(lambda)
local syt,  a,  A,  k,  b,  B,  sm;

    syt:= SYTs(lambda);

    a:= WordPartition(lambda);
    A:= Arrangements(a, Size(a));
    b:= WordPartition(ConjugatePartition(lambda));
    B:= Arrangements(b, Size(b));
    k:= List(syt, x -> [Position(A, WordsTableau(x).rows), Position(B, WordsTableau(x).cols)]);

    sm:= SpechtMatSymm(A, B);

return rec(sm:= sm, A:= A, B:= B, syt:= syt, k:= k);
end;



####Section-5. Representing matrices


#Representing matrix corresponding to the permutation sigma of symmetric group
SpechtRepPerm:= function(specht, perm)
local pi, rows, cols, i, stdrows, stdcols, stdrowspermuted, stdcolspermuted, m;

    pi:= Permutation(perm, specht.A, Permuted);
    #rows:= specht.k;
    cols:= List(specht.k, i -> i[2]);
    #stdrows:= TransposedMat(specht.sm){rows};
    stdcols:= TransposedMat(specht.sm){cols};
    #stdrowspermuted:= List(stdrows, l -> Permuted(l, pi));
    stdcolspermuted:= List(stdcols, l -> Permuted(l, pi));
    m:= List(stdcolspermuted, l -> SolutionMat(stdcols, l));

return m;
end;



####Section-6. Characters and Character table


#Characters correspnding to a partition lambda for all the class reps
SymmCharacter:= function(lambda, reps)
local specht;
    specht:= SpechtSymm(lambda);
return List(reps, sigma -> Trace(SpechtRepPerm(specht, sigma)));
end;

#Character table for all the partitions lambda of n
SymmCharTable:= function(n)
local P, reps, CharTable;
    P:= Partitions(n);
    reps:= List(P, SymmRep);
    CharTable:= List(P, lambda -> SymmCharacter(lambda, reps));
return CharTable;
end;





