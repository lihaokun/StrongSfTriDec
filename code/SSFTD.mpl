with(Groebner):

################ proc PolylistToNormal
# input: 
# Polylist: a nonempty list of nonzero polynomials which are different from each other (list)
# VarList: a list of variables which appear in Polylist (list)
# output: If Polylist has finite solutions, then the output is a strong triangular decomposition (STD) of Polylist.
#         (a row vector of some row vectors)
#         Else FAIL.
PolylistToNormal := proc(PolyList, VarList)
local i, k, ans, TriList, j;
for i from 1 to nops(PolyList) do
    if type(PolyList[i], constant)=true then
       return Vector[row]();
    end if;
end do;
TriList := IsTri(PolyList, VarList);
if TriList[1]=true then
    if IniConstant(PolyList, TriList[2])=0 then 
        if nops(PolyList)=nops(VarList) then 
            ans := Vector[row](nops(VarList));
            for i from 1 to nops(TriList[3]) do
                k := TriList[3][i];
                ans[-i] := PolyList[k];
            end do;
            for i from 2 to nops(VarList) do
                ans[i] := NormalForm(ans[i], [seq(ans[j], j=1..i-1)], plex(op(VarList)));
            end do;
            return Vector[row](1, fill = ans);
        else           
            error "FAIL1: This is not a zero-dimensional system."; 
        end if;
    else
        return SubPolylistToNormal(PolyList, VarList, 1, 1);
    end if;
else 
    return SubPolylistToNormal(PolyList, VarList, 2, 1);
end if;
end proc:

################ proc SubPolylistToNormal
# GBmethod: 0: fgb+convert
#           1: buchberger
#           2: the first time 0, else 1 (def)
# SATGBmethod: 0: fgb+convert
#              1: buchberger
SubPolylistToNormal := proc(PolyList, VarList, GBmethod := 2, SATGBmethod := 1)
local ComputedSet, GBmethod1, SplitSet, P, GB_Grad, GB_Lex, wCharList, AbnormalNum, IniNum, GB, AddF, i, GB_mainvar, lindex, lnum;
ComputedSet := Vector[row]();   # ComputedSet is a row vector of some row vectors
SplitSet := Vector[row]();      # SplitSet is a row vector of some lists
SplitSet(1) := PolyList;
GBmethod1 := GBmethod;
lindex := 1;
lnum := 1;
while lindex<=lnum do
    P := SplitSet[lindex];
    lindex := lindex+1;
    if GBmethod1=1 then
        GB_Lex := Basis(P, plex(op(VarList)), method = Buchberger);
    else
        GB_Grad := Basis(P, tdeg(op(VarList)), method = fgb);
        GB_Lex  := Basis(GB_Grad, plex(op(VarList)), method = convert);
        if GBmethod1=2 then
            GBmethod1 := 1;
        end if;
    end if;
    if GB_Lex <> [1] then
       GB_mainvar := [seq(MainVar(GB_Lex[i], VarList), i=1..nops(GB_Lex))];
       if lindex=2 then
           if not(IsZeroDim(GB_Lex, VarList)) then
              error "FAIL2: This is not a zero-dimensional system.";  
           end if;    
       end if;
       wCharList := wChar(GB_Lex, VarList, GB_mainvar); # wCharList is a row vector
       AbnormalNum := IsNormal(wCharList, VarList);
       if AbnormalNum = 0 then
            ComputedSet(numelems(ComputedSet)+1) := wCharList;
       else
            IniNum := SquareFree(primpart(lcoeff(wCharList[AbnormalNum], VarList[-AbnormalNum])));
            GB := SaturIdeal(IniNum, [seq(wCharList[i], i=1..AbnormalNum-1)], VarList, SATGBmethod); # GB is a row vector
            AddF := Vector[row]();
            for i from 1 to numelems(GB) do
                if NormalForm(GB[i], [seq(wCharList[i], i=1..AbnormalNum-1)], plex(op(VarList)))<>0 then
                    AddF(numelems(AddF)+1) := GB[i]; 
                end if;
            end do;
            SplitSet(++lnum):= [op(GB_Lex), seq(AddF[i], i=1..numelems(AddF))];
            SplitSet(++lnum):= [op(GB_Lex), IniNum];
       end if;
    end if;
end do;
return ComputedSet;      
end proc:

################ proc NormalToSquarefree
# input: 
# NormalChain: a strong chain (a row vector)
# VarList: a list of variables which appear in Polylist (list)
# output: 
# ans: a strong square-free triangular decomposition (SSFTD) of NormalChain   
#         (a row vector of some row vectors) 
NormalToSquarefree := proc(NormalChain, VarList, SATGBmethod:=1)
local NormalSet, ans, P, AbNum, temp, tempSet, f, GB, AddF, i, r1, r2, lindex, lnum;
NormalSet := Vector[row]();   # NormalSet is a vector of some row vectors
NormalSet(1) := NormalChain;     
ans := Vector[row]();         # ans is a vector of some row vectors
lindex := 1;
lnum := 1;
while lindex<=lnum do
   P := NormalSet[lindex];           # P is a row vector
   lindex := lindex+1;
   AbNum := IsSquareFree(P, VarList);
   if AbNum=0 then
        ans(numelems(ans)+1) := P;
   elif AbNum=1 then
        temp := factors(P[1]);
        tempSet := [seq(temp[2][i][1], i = 1 .. nops(temp[2]))];
        for i from 1 to nops(tempSet) do
            P(1) := tempSet[i];
            NormalSet(++lnum) := Vector[row](P);
        end do;
    else
        f := SquareFree(diff(P[AbNum], VarList[-AbNum]));  
        GB := SaturIdeal(f, [seq(P[i], i=1..AbNum)], VarList, SATGBmethod); # GB is a row vector
        AddF := Vector[row]();
        for i from 1 to numelems(GB) do
            if NormalForm(GB[i], [seq(P[i], i=1..AbNum)], plex(op(VarList)))<>0 then
                AddF(numelems(AddF)+1) := GB[i]; 
            end if;
        end do;
        r1 := SubPolylistToNormal([seq(P[i], i=1..numelems(P)), f], VarList); # r1 is a row vector of some row vectors
        r2 := SubPolylistToNormal([seq(P[i], i=1..numelems(P)), seq(AddF[i], i=1..numelems(AddF))], VarList);
        # r2 is a row vector of some row vectors
        for i from 1 to numelems(r1) do
            NormalSet(++lnum) := r1[i];
        end do;
        for i from 1 to numelems(r2) do
            NormalSet(++lnum) := r2[i];
        end do;
    end if;
end do;
return ans;
end proc:

################ proc PolysetToSfNormal
# input: 
# Polylist: a nonempty list of nonzero polynomials which are different from each other (list)
# VarList: a nonempty list of variables
# output: 
# output: If Polylist has finite solutions, then the output is a strong square-free triangular decomposition (SSFTD) of Polylist.
#         (a row vector of some row vectors)
#         Else FAIL.
PolylistToSfNormal := proc(PolySet, VarList, SATGBmethod:=1)
local NormalDec, ans, i, r, j;
NormalDec := PolylistToNormal(PolySet, VarList);   # NormalDec is a row vector of some row vectors
if NormalDec=FAIL then
   return FAIL;
else
   ans := Vector[row]();     # ans is a row vector of some row vectors
   for i from 1 to numelems(NormalDec) do
       r := NormalToSquarefree(NormalDec[i], VarList, SATGBmethod);    # r is a row vector of some row vectors
       for j from 1 to numelems(r) do
           ans(numelems(ans)+1) := r[j];
       end do;
   end do;
   return ans;
end if;
end proc:

################ proc IsTri
IsTri := proc(PolyList, VarList)
local JudgeList, i, k, mainvarList;
JudgeList := [seq(-1, i=1..nops(VarList))];
mainvarList := [seq(MainVar(PolyList[i], VarList), i=1..nops(PolyList))];
for i from 1 to nops(PolyList) do
    member(mainvarList[i], VarList, 'k');   
    if JudgeList[k]=-1 then
        JudgeList[k] := i;
    else 
        return [false];
    end if;
end do;
return [true, mainvarList, JudgeList];
end proc:

################ proc wChar
# input:
# GroeBasis: the reduced lex Groebner basis w.r.t. VarList[1]>...>VarList[n]
# VarList: the variable list of GroeBasis
# mainvar: the main variable list of GroeBasis such that the main variable of GroeBasis[i] is mainvar[i]
# output: 
# wCharList: the W-characteristic list of GroeBasis (row vector)
wChar := proc(GroeBasis, VarList, mainvar)
local k, i, PolySet, wCharList, wCharPrep, j;
PolySet := Vector[row](nops(VarList));
for k from 1 to nops(VarList) do
    PolySet[k] := Vector[row]();
end do;
for i from 1 to nops(GroeBasis) do
    member(mainvar[i], VarList, 'k');
    PolySet[k](numelems(PolySet[k])+1) := GroeBasis[i];
end do;
wCharList := Vector[row](nops(VarList));
for i from 1 to nops(VarList) do
    wCharPrep := PolySet[i][1];
    for j from 2 to numelems(PolySet[i]) do 
        if TestOrder(LeadingMonomial(PolySet[i][j], plex(op(VarList))), LeadingMonomial(wCharPrep, plex(op(VarList))), plex(op(VarList))) then
           wCharPrep := PolySet[i][j];
        end if;
    end do;
    wCharList[-i] := wCharPrep;
end do;
return wCharList;
end proc:

################ proc IsNormal
# input:
# TriSet: a zero-dim triangle set T=[T1,...,Tn] such that 0<lv(T1)<...<lv(Tn) (row vector)
# VarList: the list of main variables of TriSet such that the main variable of TriSet[i] is VarList[-i] (list)
# output: 
# NormNum: if Triset is normal, then return 0 
# else return the smallest integer (>1) such that [T1,...,Tk] is abnormal
IsNormal := proc(TriSet, VarList)
local NormNum, i;
NormNum := 0;
for i from 1 to numelems(TriSet) do    # Note that Triset[1] is a univariate polynomial.
    if type(lcoeff(TriSet[i], VarList[-i]), constant)=false then   
       NormNum := i; 
       break;
    end if;
end do;
return NormNum;
end proc:

################ proc IsNormalSpe
# input:
# PolyList: a polynomial list which is a out-of-order triangle set (a list)
# mainvarList: lv(PolyList[i]) = mainvarList[i]
# output: 
# NormNum: if all initials of PolyList are constants, then return 0; else return 1
IniConstant := proc(PolyList, mainvarList)
local i;
for i from 1 to nops(PolyList) do    # Note that Triset[1] is a univariate polynomial.
    if type(lcoeff(PolyList[i], mainvarList[i]), constant)=false then   
       return 1;
    end if;
end do;
return 0;
end proc:

################ proc IsSquareFree
# input:
# TriSet: a triangle set T=[T1,...,Tn] such that 0<lv(T1)<...<lv(Tn) (a row vector)
# (a list)
# VarList: the list of main variables of TriSet such that the main variable of TriSet[i] is VarList[-i]
# output: 
# NormNum: if Triset is square-free, then return 0 
# else return the smallest integer such that [T1,...,Tk] is not squarefree
IsSquareFree := proc(TriSet, VarList)
local NormNum, j, i, dis, Tri;
NormNum := 0;
if primpart(discrim(TriSet[1], VarList[-1]))=0 then  
   return 1;
else
   for i from 2 to numelems(TriSet) do
        dis[i] := primpart(discrim(TriSet[i], VarList[-i])); 
        Tri := [seq(TriSet[j], j=1..i-1)];
        if ResTri(dis[i], Tri, VarList)=0 then
           NormNum := i; break;
        end if;
        if NormNum <> 0 then break; end if;
    end do;
    return NormNum;
end if;
end proc:

################ proc ResTri
# input:
# P : a polynomial
# TriSet: a triangle set T=[T1,...,Tn] such that 0<lv(T1)<...<lv(Tn)   (a list)
# VarList: the list of main variables of TriSet such that the main variable of TriSet[i] is VarList[-i] 
# output: 
# F: Res(P, TriSet)
ResTri := proc(P, TriSet, VarList)
local F, n,i,j,temp,tempSet1,tempSet2;
F := P;
for n from nops(TriSet) by -1 to 1 do
    F := primpart(resultant(F, TriSet[n], VarList[-n]));
end do;
return F;
end proc:

################ proc SaturIdeal
# input:
# Poly : a polynomial
# PolyList: a list of polynomials (a list)
# SATGBmthod: 0: fgb+convert; 1: buchberger
# output: 
# ans: the lex reduced Groebner basis of <op(PolyList)>:Poly^{infinity} (a vector)
SaturIdeal := proc(Poly, PolyList, VarList, SATGBmethod:=0) 
local Z, GB_Grad, GB_Lex, i, ans;
ans := Vector[row]();
if SATGBmethod=0 then
    GB_Grad := Basis([op(PolyList), 1-Poly*Z], tdeg(Z, op(VarList)), method = fgb);
    GB_Lex  := Basis(GB_Grad, plex(Z, op(VarList)), method = convert);
else
    GB_Lex  := Basis([op(PolyList), 1-Poly*Z], plex(Z, op(VarList)), method = buchberger);
end if;
for i from 1 to nops(GB_Lex) do
    if has(GB_Lex[i], Z)=false then
       ans(numelems(ans)+1) := GB_Lex[i];
    end if;
end do; 
return ans;
end proc:

########## proc Class, proc MainVar, proc WuInitial
# input:
# f: a polynomial
# ord: a list of variables of f such that ord[1]>ord[2]>... 
########## proc Class
Class := proc(f::polynom, ord::list)
local i;
option cache;
for i from 1 to nops(ord) do
	if has(f,ord[i]) then
		return i;
	end if;
end do;
return 0;
end proc:

########## proc MainVar
MainVar := proc(f::polynom, ord::list)
local i;
option cache;
for i from 1 to nops(ord) do
	if has(f, ord[i]) then
		return ord[i];
	end if;
end do;
return 0;
end proc:

########## proc WuInitial
WuInitial := proc(f::polynom, ord::list)
option cache;
if Class(f, ord)=0 then
	return 1;
else
	return primpart(lcoeff(f, MainVar(f,ord)));
end if;
end proc:

########## proc SquareFree
SquareFree := proc(poly)
option cache;
local FactorList,i;
FactorList := sqrfree(poly);
return mul(FactorList[2][i][1], i = 1 .. nops(FactorList[2]));
end proc:

########## proc IsZeroDim
IsZeroDim := proc(GBlex, VarList)
local JudgeList,i,IndSet,j;
JudgeList := [seq(0, i=1..nops(VarList))];
for i from 1 to nops(GBlex) do
   IndSet := indets(LeadingMonomial(GBlex[i], plex(op(VarList))));
   if nops(IndSet)=1 then
       for j from 1 to nops(VarList) do
           if IndSet={VarList[j]} then
               JudgeList[j] := 1;
               break;
           end if;
       end do;
   end if;
end do;
for i from 1 to nops(JudgeList) do
   if JudgeList[i]=0 then
       return false;
   end if;
end do;
return true;
end proc: