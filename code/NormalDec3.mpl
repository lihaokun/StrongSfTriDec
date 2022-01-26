################ NormalDec3: 
################ (1) 将NormalDec2中的proc PolylistToNormal, proc RSD, proc PolylistToSfNormal, proc NormalToSquarefree增加################     Grobner基计算策略
################ (2) 将NormalDec2中的IdealMembership计算改为NormalForm                  

with(Groebner):

################ proc PolylistToNormal
# input: 
# Polylist: a nonempty list of nonzero polynomials which are different from each other (list)
# VarList: a list of variables which appear in Polylist (list)
# output: if Polylist has finite solutions, the output is a normal and no intersection decomposition in Dong and Mou 2019 
#         (a row vector of some row vectors)
#         else FAIL
PolylistToNormal := proc(PolyList, VarList)
local i, k, ans, TriList, j;
for i from 1 to nops(PolyList) do
    if type(PolyList[i], constant)=true then
       return Vector[row]();
    end if;
end do;
TriList := IsTri(PolyList, VarList);
# TriList = [true, mainvarList, JudgeList], where 
# (1) lv(PolyList[i]) = mainvarList[i]
# (2) PolyList为乱序三角列, PolyList[JudgeList[i]]正序的位置为倒数第i个
# 或者 TriList = [false]
# print("TriList", TriList);
if TriList[1]=true then
    if IniConstant(PolyList, TriList[2])=0 then # PolyList是初式为非零常数的三角列, 此时PolyList是Groebner基
        if nops(PolyList)=nops(VarList) then # 若还有lv(PolyList)=VarList, 则PolyList必有有限个解
            ans := Vector[row](nops(VarList));
            for i from 1 to nops(TriList[3]) do
                k := TriList[3][i];
                ans[-i] := PolyList[k];
            end do;
            # print("ans", ans);
            for i from 2 to nops(VarList) do
                ans[i] := NormalForm(ans[i], [seq(ans[j], j=1..i-1)], plex(op(VarList)));
            end do;
            # print("NormalForm ans", ans);
            return Vector[row](1, fill = ans);
        else           
            # 注意到PolyList是Groebner基. 若存在VarList[i], 使得对任意的g \in PolyList, lv(g) \ne VarList[i], 则PolyList必有无限个解
            # (ipad上证明的消去理想命题的逆否命题)
            # print("FAIL1: This is not a zero-dimensional system."); 
            # return FAIL;
            error "FAIL1: This is not a zero-dimensional system."; 
        end if;
    else
        return SubPolylistToNormal(PolyList, VarList, 1, 1);
    end if;
else # PolyList不是初式为非零常数的三角列, 此时只能通过计算Groebner基判断PolyList解的个数是否有限
    # print("SubPolylistToNormal");
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
    # print("lindex", lindex);
    # print("P", P);
    lindex := lindex+1;
    # print("GBmethod1", GBmethod1);
    if GBmethod1=1 then
        GB_Lex := Basis(P, plex(op(VarList)), method = Buchberger);
        # print("GB_Lex:", GB_Lex);
    else
        GB_Grad := Basis(P, tdeg(op(VarList)), method = fgb);
        # print("GB_Grad:", GB_Grad);
        GB_Lex  := Basis(GB_Grad, plex(op(VarList)), method = convert);
        # print("GB_Lex:", GB_Lex);
        if GBmethod1=2 then
            GBmethod1 := 1;
        end if;
    end if;
    # print("GB_Lex", GB_Lex);
    if GB_Lex <> [1] then
       GB_mainvar := [seq(MainVar(GB_Lex[i], VarList), i=1..nops(GB_Lex))];
       # print("GB_mainvar:", GB_mainvar);
       if lindex=2 then
           if not(IsZeroDim(GB_Lex, VarList)) then
              error "FAIL2: This is not a zero-dimensional system.";  
           end if;    
       end if;
       wCharList := wChar(GB_Lex, VarList, GB_mainvar); # wCharList is a row vector
       # print("wCharList:", wCharList, numelems(wCharList));
       AbnormalNum := IsNormal(wCharList, VarList);
       # print("AbnormalNum:", AbnormalNum);
       if AbnormalNum = 0 then
            ComputedSet(numelems(ComputedSet)+1) := wCharList;
            # print("ComputedSet:", ComputedSet);
       else
            # IniNum := primpart(lcoeff(wCharList[AbnormalNum], VarList[-AbnormalNum]));
            IniNum := SquareFree(primpart(lcoeff(wCharList[AbnormalNum], VarList[-AbnormalNum])));
            # print("wCharList[AbnormalNum]:", wCharList[AbnormalNum]);
            # print("IniNum:", IniNum);
            GB := SaturIdeal(IniNum, [seq(wCharList[i], i=1..AbnormalNum-1)], VarList, SATGBmethod); # GB is a row vector
            # print("GB:", GB);
            AddF := Vector[row]();
            for i from 1 to numelems(GB) do
                # print("NormalForm:", NormalForm(GB[i], [seq(wCharList[i], i=1..AbnormalNum-1)], plex(op(VarList))));
                if NormalForm(GB[i], [seq(wCharList[i], i=1..AbnormalNum-1)], plex(op(VarList)))<>0 then
                    AddF(numelems(AddF)+1) := GB[i]; 
                    # print("AddF:", AddF);
                end if;
            end do;
            # print("AddF:", AddF);
            # print("lnum:", lnum);
            SplitSet(++lnum):= [op(GB_Lex), seq(AddF[i], i=1..numelems(AddF))];
            # print("SplitSet:", [op(GB_Lex), seq(AddF[i], i=1..numelems(AddF))]);
            SplitSet(++lnum):= [op(GB_Lex), IniNum];
            # print("SplitSet:", [op(GB_Lex), IniNum]);
            # print("SplitSet:", SplitSet);
       end if;
    end if;
end do;
# print("numelems(ComputedSet):", numelems(ComputedSet));
return ComputedSet;      
end proc:

################ proc NormalToSquarefree
# input: 
# NormalChain: a zero-dimensional and normal chain (a row vector)
# VarList: a nonempty list of variables
# GBmethod :0 fgb 1 Buchberger
# output: 
# ans: a normal and square-free decomposition  
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
   # print("lindex:", lindex);
   # print("P:", P);
   lindex := lindex+1;
   AbNum := IsSquareFree(P, VarList);
   # print("AbNum:", AbNum);
   if AbNum=0 then
        ans(numelems(ans)+1) := P;
        # print("ans:", ans);
   elif AbNum=1 then
        temp := factors(P[1]);
        tempSet := [seq(temp[2][i][1], i = 1 .. nops(temp[2]))];
        # print("tempSet:", tempSet);
        for i from 1 to nops(tempSet) do
            P(1) := tempSet[i];
            NormalSet(++lnum) := Vector[row](P);
        end do;
    else
        f := SquareFree(diff(P[AbNum], VarList[-AbNum]));  
        # f := diff(P[AbNum], VarList[-AbNum]);
        # print("f:", f);
        GB := SaturIdeal(f, [seq(P[i], i=1..AbNum)], VarList, SATGBmethod); # GB is a row vector
        # print("GB");
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
# Polylist: a zero-dimensional nonempty set of nonzero polynomials
# VarList: a nonempty list of variables

# output: 
# ans: if PolySet is zero-dimensional, the output is a normal, square-free and no intersection decomposition 
#      (a row vector of some row vectors)
#      else FAIL
PolylistToSfNormal := proc(PolySet, VarList, SATGBmethod:=1)
local NormalDec, ans, i, r, j;
# Method:
# 0: proc PolylistToNormal和proc NormalToSquarefree中GB的计算使用fgb+convert; proc SaturIdeal中GB的计算使用fgb+convert
# 1: proc PolylistToNormal和proc NormalToSquarefree中GB的计算使用fgb+convert; proc SaturIdeal中GB的计算使用buchberger
# 2: proc PolylistToNormal中GB的计算使用策略; proc NormalToSquarefree中GB的计算使用buchberger; proc SaturIdeal中GB的计算使用buchberger  
#st := time[real]():
# if Method=2 then
#     SATGBmethod := 1;
#     NGBmethod := 2;
#     SFGBmethod := 1;
# elif Method=1 then
#     SATGBmethod := 1;
#     NGBmethod := 0;
#     SFGBmethod := 0;
# else
#     SATGBmethod := 0;
#     NGBmethod := 0;
#     SFGBmethod := 0;
# end if;
NormalDec := PolylistToNormal(PolySet, VarList);   # NormalDec is a row vector of some row vectors
if NormalDec=FAIL then
   return FAIL;
else
   # print(NormalDec);
   ans := Vector[row]();     # ans is a row vector of some row vectors
   # print("numelems(NormalDec):", numelems(NormalDec));
   for i from 1 to numelems(NormalDec) do
       r := NormalToSquarefree(NormalDec[i], VarList, SATGBmethod);    # r is a row vector of some row vectors
       # print("numelems(r):", numelems(r));
       for j from 1 to numelems(r) do
           ans(numelems(ans)+1) := r[j];
       end do;
   end do;
   # print("numelems(ans):", numelems(ans));
   return ans;
end if;
end proc:

################ proc IsTri
IsTri := proc(PolyList, VarList)
local JudgeList, i, k, mainvarList;
JudgeList := [seq(-1, i=1..nops(VarList))];
mainvarList := [seq(MainVar(PolyList[i], VarList), i=1..nops(PolyList))];
# print("JudgeList:", JudgeList);
for i from 1 to nops(PolyList) do
    member(mainvarList[i], VarList, 'k');   
    if JudgeList[k]=-1 then
        JudgeList[k] := i;
    else 
        return [false];
    end if;
    # print("JudgeList:", JudgeList);
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
    # print("Initial(TriSet[i], R)", Initial(TriSet[i], R));
    # print("type(Initial(TriSet[i], R), constant)", type(Initial(TriSet[i], R), constant));
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
    # print("Initial(TriSet[i], R)", Initial(TriSet[i], R));
    # print("type(Initial(TriSet[i], R), constant)", type(Initial(TriSet[i], R), constant));
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
# print("TriSet[1]", TriSet[1]);
# print("discrim(TriSet[1], VarList[-1]):", discrim(TriSet[1], VarList[-1]));
if primpart(discrim(TriSet[1], VarList[-1]))=0 then  
# if primpart(xdiscr(sf(TriSet[1]), VarList[-1]))=0 then 
#    print("TriSet[1]", TriSet[1], " VarList[-1]", VarList[-1]," VarList", VarList);
   return 1;
else
   for i from 2 to numelems(TriSet) do
        # print("discrim(TriSet[i], VarList[-i]):", i, " 1");
        dis[i] := primpart(discrim(TriSet[i], VarList[-i])); 
        # dis[i] := primpart(xdiscr(sf(TriSet[i]), VarList[-i])); 
        # print("discrim(TriSet[i], VarList[-i]):", i, " 2");
        Tri := [seq(TriSet[j], j=1..i-1)];
        if ResTri(dis[i], Tri, VarList)=0 then
           NormNum := i; break;
        end if;
        # print("discrim(TriSet[i], VarList[-i]):", i, " 3");
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
    # print("ResTri N:",n," 1");
    # temp := factors(F);
    # tempSet1 := [seq(temp[2][i][1], i = 1 .. nops(temp[2]))];
    # temp := factors(TriSet[n]);
    # tempSet2 := [seq(temp[2][i][1], i = 1 .. nops(temp[2]))];
    # F:=1;
    # for i from 1 to nops(tempSet1) do
    #     for j from 1 to nops(tempSet2) do
    #         F *= primpart(resultant(tempSet1[i], tempSet2[j], VarList[-n]));
    #     end do;    
    # end do;
    F := primpart(resultant(F, TriSet[n], VarList[-n]));
    # print("ResTri N:",n," 2");    
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
# print("SATGBmethod:", SATGBmethod);
# print("ans", ans);
if SATGBmethod=0 then
    GB_Grad := Basis([op(PolyList), 1-Poly*Z], tdeg(Z, op(VarList)), method = fgb);
    # print("GB_Grad:", GB_Grad);
    GB_Lex  := Basis(GB_Grad, plex(Z, op(VarList)), method = convert);
    # print("GB_Lex:", GB_Lex);
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

########## proc sf
# input: a polynomial poly, which is equal to c*f1^{s1}...fn^{sn}
# output: f1^{s1}*...*fn^{sn}
# sf := proc(poly)
# option cache;
# local fp, fp1, fp2, i;
#    fp := factors(poly);
#    # fp1:=op(1,fp);
#    # fp1:=sgn(fp1);
#    fp2 := fp[2];
#    fp1 := 1;
#    for i from 1 to nops(fp2) do
#        fp1 := fp1 * fp2[i][1];
#    od;
#    # primpart(fp1);
# return fp1;
# end:

################ proc RSD
# input: 
# NormalChain: a zero-dimensional and normal chain (a set)
# Poly: a polynomial
# VarList: a nonempty list of variables
# output: 
# if NormalChain is zero-dimensional, the output is a RSD and no intersection decomposition 
#    T_{1},...,T_{k},T_{k+1},...,T_{k+j} on the page 34 of Xia Book 
#    ans1: {T_{1},...,T_{k}} such that V(T_{i}) \intersect V(Poly) = {}
#    ans2: {T_{k+1},...,T_{k+j}} such that V(T_{i}) \subseteq V(Poly)
#    (two sets of some lists)
# else FAIL
# RSD := proc(NormalChain, Poly, VarList, GBmethod:=1, SATGBmethod:=1)
# local R, NormalSet, ans1, ans2, P, premR, QuoIdeal, GB, AddF, PolySet, NormalDecom, i, j;
# R := PolynomialRing(VarList);
# NormalSet := [NormalChain];
# NormalSet: a set of some lists
# ans1 := [];
# ans2 := [];
# while nops(NormalSet)>0 do
#    P := NormalSet[1];
#    NormalSet := subsop(1=NULL, NormalSet);
#    if P <> [1] then
#        premR := PremTri(Poly, P, R);
#        if premR=0 then
#             ans2 := [op(ans2), P];
#        elif ResTri(Poly, P, R)<>0 then
#             ans1 := [op(ans1), P];
#        else
#             GB := SaturIdeal(Poly, P, VarList, SATGBmethod);
#             AddF := [];
#             for i from 1 to nops(GB) do
#                 #if IdealMembership(GB[i], PolynomialIdeal(op(P)))=false then
#                 if Groebner:-NormalForm(GB[i], P, plex(op(VarList)))<>0 then
#                     AddF := [op(AddF), GB[i]]; 
#                 end if;
#             end do;
#             PolySet := [[op(P), Poly], [op(P), op(AddF)]];
#             for i from 1 to nops(PolySet) do
#                 NormalDecom := PolylistToNormal(PolySet[i], VarList); 
#                 for j from 1 to nops(NormalDecom) do
#                     NormalSet := [op(NormalSet), NormalDecom[j]];
#                 end do;
#             end do;
#        end if;        
#    end if;
# end do;
# return ans1, ans2;
# end proc:

################ proc PremTri (RSD的子算法, 先不管)
# input:
# P : a polynomial
# TriSet: a triangle set T=[T1,...,Tn] such that 0<lv(T1)<...<lv(Tn)
#        (a list)
# R: PolynomialRing(VarList)
# output: 
# F: prem(P, TriSet)
# PremTri := proc(P, TriSet, R)
# local F, n;
# F := P;
# for n from nops(TriSet) by -1 to 1 do
#     if type(TriSet[n], constant) = false then 
#         F := prem(F, TriSet[n], MainVariable(TriSet[n], R));     # RSD的子算法, 先不管
#     else 
#         F := 0; break;
#     end if;
# end do;
# return F;
# end proc: