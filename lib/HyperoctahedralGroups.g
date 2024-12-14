####Section-1. The group, generators and class reps


#Monomial group (as a subgroup of S_2n) generators as perms on 2n points [1,2,...,n,2n,2n-1,...,n+1] = [1,2,...n,-n,-n-1,...,]
HypoGens:= function(n)
local i, gens;
    gens:= [];
        for i in [0..n-2] do
            Add(gens, (i+1,i+2)(2*n-i,2*n-i-1));
        od;
    Add(gens, (1, 2*n), 1);
return gens;
end;


#Hyperoctahedral Group
HypoGroup:= function(n)
#return Centralizer(SymmetricGroup(2*n), PermList(Reversed([1..2*n])));
return GroupWithGenerators(HypoGens(n));
end;


#Class representatives as a generator word
HypoRepGenWord:= function(lambda)
    local w, o, l, pcycle, ncycle;

    pcycle:= function(o,l)
    return o+[2..l]; 
    end;
    
    ncycle:= function(o,l)
    return Concatenation([o+1,o..1],[2..o+l]);
    end;

    w:=[];
    o:= 0;   
    for l in Reversed(lambda[2]) do
        Append(w, ncycle(o,l));
        o:= l+o;
    od;
    
    for l in lambda[1] do          
        Append(w, pcycle(o,l));
        o:= l+o;
    od;
    return w;
end;


#Class representatives for a set of bipartitions
HypoReps:= function(all_bipartitions)
    local n, gens, classes, conj_classes, c;
    n:= Sum(Sum(all_bipartitions[1]));
    gens:= HypoGens(n);
    classes:= List(all_bipartitions, HypoRepGenWord);
    classes[Position(classes, [])]:= [1,1];
    conj_classes:= List(classes, c -> Product(gens{c}));
    return conj_classes;
end;



####Section-2. Bipartitions and words


#Bipartitions of a number n
BiPartitions:= function(n)
return PartitionTuples(n, 2);
end;


#Conjugate bipartition
ConjugateBiPartition:= function(lambda)
return Reversed(List(lambda, AssociatedPartition));
end;


#Word corresponding to a bipartition
WordBiPartition:= function(lambda)
local WordPartition, w_1, w_2, word;
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
    w_1:= List(WordPartition(lambda[1]), String);
    w_2:= WordPartition(lambda[2]);
    word:= Concatenation(w_1, w_2, -Reversed(w_2), Reversed(w_1));
return word;
end;


#Arrangements of words by the action of hyperoctahdral group
HypoArrangements:= function(w)
local B_nGroup, a1, a2, sigma, pi;
    
    B_nGroup:= function(n)
        return Centralizer(SymmetricGroup(2*n), PermList(Reversed([1..2*n])));
    end;

    a1:= Orbit(B_nGroup(Length(w)/2), w, Permuted);
    a2:= Orbit(HypoGroup(Length(w)/2), w, Permuted);
    sigma:= Sortex(ShallowCopy(a1));
    pi:= Sortex(ShallowCopy(a2));
return Permuted(a2, pi*sigma^-1);
end;

#Bipartition corresponding to a word
BiPartitionWord:= function(w)
local lambda, a;
    lambda:= [[],[]];
    for a in w{[1..Length(w)/2]} do
        if IsInt(a) then 
            a:= AbsInt(a);
            if IsBound(lambda[2][a]) then
                lambda[2][a]:= lambda[2][a]+1;
            else
                lambda[2][a]:= 1;
            fi;
        else 
            a:= Int(a);
            if IsBound(lambda[1][a]) then
                lambda[1][a]:= lambda[1][a]+1;
            else
                lambda[1][a]:= 1;
            fi;
        fi;
    od;
return lambda;
end;


#Mirrored word corresponding to a word of length n and returns a word of length 2n.
MirroredWord:= function(w)
local w1, w2, i;
    w1:= [];
    w2:= [];
    for i in w do
        Add(w1, i);
        if IsInt(i) then
            Add(w2, -i);
        else
            Add(w2, i);
        fi;
    od;
return Concatenation(w1, Reversed(w2));
end;



#####Section-3. Bitableaux and pairs of words


#Standard Young biltitableaux (SYBTs) for a multipartition lambda
#tuple = [lambda1, lambda2]
SYBTs:= function(tuple)
local   isOneHook,  removeOneHook,  addOneHook,  n,  list,  i, k, lambda,
            new,  t;
#here lambda is an ordinary partition
    isOneHook:= function(lambda, i)
        return i = Length(lambda) or lambda[i] > lambda[i+1];
    end;

    removeOneHook:= function(tuple, k, i)
        local lambda, new;
        lambda:= ShallowCopy(tuple[k]);
        new:= ShallowCopy(tuple);
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
    if tuple = [[],[]] then
        return [[[[]],[[]]]];
    fi;

    # initialize
    n:= Sum(tuple, Sum);
    list:= [];

    # loop
    for k in Reversed([1..Length(tuple)]) do 
        lambda:= tuple[k];
        for i in Reversed([1..Length(lambda)]) do
            if isOneHook(lambda, i) then
                new:= removeOneHook(tuple, k, i);
                for t in SYBTs(new) do
                    addOneHook(t, k, i, n);
                    Add(list, t);
                od;
            fi;
        od;
    od;
return list;
end;


#Canonnical biltitableau for a multipartition lambda
CanonicalBiTableau:= function(lambda)
local CanonicalTableau, t, t1, o, l;

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

    t:= [];
    t1:= [];
    Add(t, CanonicalTableau(lambda[1]));
    o:= Sum(lambda[1]);
        for l in lambda[2] do
            Add(t1, o + [1..l]);
            o:= o + l;
        od;
        Add(t, t1);
return t;
end;



#Word corresponding to a biltitableau
WordsBiTableau:= function(tab)
local rows, cols, i, k, a, b, tab1, tab2;
    rows:= [];
    cols:= [];
    #tableau 1
    tab1:= tab[1];
        for i in [1..Length(tab1)] do
            for k in [1..Length(tab1[i])] do
                a:= tab1[i][k];
                if a > 0 then
                    rows[a]:= String(i);
                    cols[a]:= k;
                else
                    rows[-a]:= String(i);
                    cols[-a]:= -k;
                fi;
            od;
        od;
    #tableau 2
    tab2:= tab[2];
        for i in [1..Length(tab2)] do
            for k in [1..Length(tab2[i])] do
                b:= tab2[i][k];
                if b > 0 then
                    rows[b]:= i;
                    cols[b]:= String(k);
                else
                    rows[-b]:= -i;
                    cols[-b]:= String(k);
                fi;
            od;
        od;
return List([rows, cols], MirroredWord);
end;


#Tableau corresponding to a word
BiTableauWords:= function(u,v)
local lambda, n, pair, pairTransposed, tableau, coords, t1, t2, i;
    lambda:= BiPartitionWord(u);
    n:= Sum(List(lambda, Sum));
    pair:= [u,v];
    pairTransposed:= TransposedMat(pair);
    tableau:= CanonicalBiTableau(lambda);
    coords:= pairTransposed{[1..n]};
    t1:= tableau[1];
    t2:= tableau[2];
    if Size(Set(coords)) < n then
        return false;
    else
        for i in coords do
            if Number(i, IsInt) <> 1 then
                return false;
            elif IsString(i[1]) = true then
#                if i[2] = AbsInt(i[2]) then
#                    t1[Int(i[1])][i[2]]:= Position(coords, i);
                    t1[Int(i[1])][AbsInt(i[2])]:= SignInt(i[2]) * Position(coords, i);
#                else
#                    t1[Int(i[1])][i[2]]:= -1 * Position(coords, i);
#                fi;
            else
                t2[AbsInt(i[1])][Int(i[2])]:= SignInt(i[1]) * Position(coords, i);
            fi;
        od;
    fi;
return [t1, t2];
end;

####Section4. Specht object


#Young character of two words u and v
YoungCharHypo:= function(w1, w2)
local c, p, n, list, l, pi, lambda, t, pi0, u1, w;
    c:= TransposedMat([w1, w2]);
    if Size(Set(c)) < Length(c) then
        return 0;
    fi;
    p:= Set(c, x -> Number(x, IsInt));
    if p <> [1] then 
        return 0;
    fi;
    lambda:= BiPartitionWord(w1);
    t:= CanonicalBiTableau(lambda);    
    w:= WordsBiTableau(t);
    pi0:= Sortex(ShallowCopy(TransposedMat(w)));
    pi:= Sortex(ShallowCopy(c));
    u1:= pi/pi0;
    if u1 <> () then
        n:= (LargestMovedPoint(u1) + SmallestMovedPoint(u1)-1)/2;
        list:= (ListPerm(u1){[1..n]} + n) mod (2*n + 1) - n;
        l:= List(list, AbsInt);
        pi:= PermList(l);
        return SignPerm(u1 * pi);
    else
        return 1;
    fi;
end;

#Specht matrix corresponding to the set of arrangements of the row word and column words, A and B respectively
SpechtMatHypo:= function(A, B)
local u, v, matrix, row;
    matrix:= [];
        for u in A do
            row:= [];
            for v in B do
                Add(row, YoungCharHypo(u,v));
            od;
            Add(matrix, row);
        od;
return matrix;
end;

#Specht object to record all the previous information needed for further concepts
SpechtHypo:= function(lambda)
local w1, A, w2, B, mu, sm, sybt, words, k;
    w1:= WordBiPartition(lambda);
    A:= HypoArrangements(w1);

    mu:= ConjugateBiPartition(lambda);
    w2:= WordBiPartition(mu);
    B:= HypoArrangements(w2);

    sm:= SpechtMatHypo(A, B);
    sybt:= SYBTs(lambda);

    words:= List(sybt, i -> WordsBiTableau(i));
    k:= List(words, i -> [Position(A, i[1]), Position(B, i[2])]);

return rec(sm:= sm, A:= A, B:= B, k:= k, sybt:= sybt);
end;



####Section-5. Representing matrices


###Representing matrix corresponding to a signed permutation element in the hyperoctahedral group
SpechtRepHypo:= function(specht, sigma)
local act, pi, rows_label, new_rows_label, sm_rows;
    act:= ActionHomomorphism(HypoGroup(Length(specht.A[1])/2), specht.A, Permuted);
    pi:= sigma^act;
    rows_label:= List(specht.k, i -> i[1]);
    new_rows_label:= OnTuples(rows_label, pi);
    sm_rows:= List(specht.k, i -> specht.sm[i[1]]);
return List(new_rows_label, i -> SolutionMat(sm_rows, specht.sm[i]));
end;



####Section-6. Characters and Character table


#Characters correspnding to a bipartition lambda for all of the generators of hypo group
HypoCharacterWordGens:= function(lambda, gens)
    local n, Bipartitions, specht, classes, list;
    n:= Sum(lambda[1])+Sum(lambda[2]);
    Bipartitions:= BiPartitions(n);
    specht:= SpechtHypo(lambda);
    classes:= List(Bipartitions, HypoRepGenWord);
    classes[1]:= [1,1];
    list:= List(gens, sigma -> SpechtRepHypo(specht, sigma));
    return List(classes, c -> TraceMat(Product(list{c})));
end;


#Characters correspnding to a bipartition lambda for all of the class reps (permutations)
HypoCharacter:= function(lambda, reps)
    local specht;
    specht:= SpechtHypo(lambda);
    return List(reps, sigma -> TraceMat(SpechtRepHypo(specht, sigma)));
end;

#Character table for all the bipartitions lambda of n
HypoCharTable:= function(n)
    local P, reps, CharTable;
    P:= BiPartitions(n);
    reps:= HypoReps(P);
    CharTable:= List(P, lambda -> HypoCharacter(lambda, reps));
    return CharTable;
end;



