######## tianqi's zhan99
read "tst58.mpl";
read "NormalDec3.mpl";
# currentdir(FileTools[CanonicalPath]("../RSD_code/")); read "database1.mpl"; read "RealRoot.mpl";
# read "C:/Users/zhaot/Documents/GitHub/FGT_realroot/RSD/RSD_code/tst58.mpl";
# read "C:/Users/zhaot/Documents/GitHub/FGT_realroot/RSD/RSD_code/NormalDec3.mpl";
# read "C:/Users/zhaot/Documents/GitHub/FGT_realroot/RSD/RSD_code/cm.mpl";
# read "C:/Users/zhaot/Documents/GitHub/FGT_realroot/RSD/RSD_code/example_xia2006.mpl";

######## tianqi's Legion
# read "C:/Users/天琪/Documents/我的坚果云/RSD/RSD_code/tst58.mpl";
# read "C:/Users/天琪/Documents/我的坚果云/RSD/RSD_code/NormalDec2.mpl";
# read "C:/Users/天琪/Documents/我的坚果云/RSD/RSD_code/cm.mpl";

with(RegularChains):
with(ChainTools):
with(RootFinding):
with(ListTools):
with(PolynomialIdeals):

################ proc RealRoot
RealRoot := proc(PolyList, VarList, Widthgoal)
local SfNormalDec, RootInterval, i, st, st1, st2, r, j;
#print("GBmethod is", GBmethod);
st := time[real]():
SfNormalDec := PolylistToSfNormal(PolyList, VarList);   # SfNormalDec is a row vector of some row vectors
st1 := time[real]()-st;
print("the time of SfNormalDec is", st1);
RootInterval := Vector[row]();    # RootInterval is a row vector of some row vectors
for i from 1 to numelems(SfNormalDec) do
   #print(triRoot(SfNormalDec[i], Reverse(VarList), Widthgoal));
   r := triRoot([seq(SfNormalDec[i][j], j=1..numelems(SfNormalDec[i]))], Reverse(VarList), Widthgoal);
   for j from 1 to nops(r) do
       RootInterval(numelems(RootInterval)+1) := r[j];
   end do;
end do;
st2 := time[real]()-st;
print("the time of RealRoot is", st2);
# print("RootInterval are", RootInterval);
print("numelems(RootInterval) is", numelems(RootInterval));
return RootInterval;
end proc:

################ proc ZeroRadical
ZeroRadical := proc(PolyList, VarList) 
local SfNormalDec, RadicalIdeal, i, j,st;
st:=time[real]();
SfNormalDec := PolylistToSfNormal(PolyList, VarList);
print("the time of PolylistToSfNormal is", time[real]()-st);
if numelems(SfNormalDec)=0 then
   print("the time of ZeroRadical is", time[real]()-st);
   return PolynomialIdeal(1);
else
   RadicalIdeal := PolynomialIdeal(seq(SfNormalDec[1][j], j=1..numelems(SfNormalDec[1])));
   if numelems(SfNormalDec)=1 then
      print("the time of ZeroRadical is", time[real]()-st);
      return RadicalIdeal; 
   else
      for i from 2 to numelems(SfNormalDec) do
         RadicalIdeal := Intersect(RadicalIdeal, PolynomialIdeal(seq(SfNormalDec[i][j], j=1..numelems(SfNormalDec[i]))));
      end do;
      print("the time of ZeroRadical is", time[real]()-st);
      return RadicalIdeal;
   end if;
end if;
end proc:

################ proc ZeroRadical1
ZeroRadical1 := proc(PolyList, VarList) 
local SfNormalDec, RadicalIdeal, i, j, st, s, temp, RadicalGB;
st:=time[real]();
SfNormalDec := PolylistToSfNormal(PolyList, VarList);
print("the time of PolylistToSfNormal is", time[real]()-st);
if numelems(SfNormalDec)=0 then
   print("the time of ZeroRadical1 is", time[real]()-st);
   return PolynomialIdeal(1);
else
   # RadicalIdeal := PolynomialIdeal(seq(SfNormalDec[1][j], j=1..numelems(SfNormalDec[1])));
   RadicalGB := [seq(SfNormalDec[1][j], j=1..numelems(SfNormalDec[1]))];
   if numelems(SfNormalDec)=1 then
      print("the time of ZeroRadical1 is", time[real]()-st);
      return RadicalGB; 
   else
      for i from 2 to numelems(SfNormalDec) do
         temp := [seq(SfNormalDec[i][j], j=1..numelems(SfNormalDec[i]))];
         RadicalGB := [op(map(x->s*x, RadicalGB)), op(map(x->(1-s)*x, temp))];
         RadicalGB := Basis(RadicalGB, plex(s, op(VarList)), method = Buchberger);
         RadicalIdeal := [];
         for j from 1 to nops(RadicalGB) do
            if has(RadicalGB[j], s)=false then
               RadicalIdeal := [op(RadicalIdeal), RadicalGB[j]];
            end if;
         end do;
         RadicalGB := RadicalIdeal;
      end do;
      print("the time of ZeroRadical1 is", time[real]()-st);
      return RadicalGB;
   end if;
end if;
end proc:

################ proc MapleSfNormal
MapleSfNormal := proc(PolyList, VarList)
local R, dec, newdec, st, st1, st2;
st := time[real]():
R := PolynomialRing(VarList);
dec := Triangularize([op(PolyList)], R, output=lazard, radical=yes);
st1 := time[real]()-st;
print("the time of Triangularize is", st1);
newdec := SeparateSolutions(dec, R);
st2 := time[real]()-st;
print("the time of SeparateSolutions is", st2);
return dec, newdec;
end proc:

################ proc testSf
testSf := proc(ex, m:=-1, n:=-1)
local i,st,tm,tn;
tm:=m;tn:=n;  
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do  
   print("###");    
   print("num:", i);      
   try 
      st := time[real]():
      timelimit[real](3600, print(time[real](PolylistToSfNormal(op(ex[i])))));      
      print("Time:", time[real]()-st);      
   catch: 
      print("Timeout!", time[real]()-st);      
   end try;  
end do;  
end proc:

################ proc testRealRoot
testRealRoot := proc(ex, m:=-1, n:=-1, expect:={})
local i,st,tm,tn;
tm:=m;tn:=n;  
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do  
   print("###");    
   print("num:", i);
   if i in expect then
      print("Timeout!",4000);
   else      
      try 
         st := time[real]():
         timelimit[real](3600, RealRoot(op(ex[i]), 1));      
      catch: 
         print("Timeout!", time[real]()-st);      
      end try;  
   end if;
end do;  
end proc:

################ proc testZeroRadical
testZeroRadical := proc(ex, m:=-1, n:=-1)
local i,st,ZR,tm,tn;
tm:=m;tn:=n;  
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do  
   print("###");    
   print("num:", i);      
   try 
      st := time[real]():
      timelimit[real](3600, ZeroRadical(op(ex[i])));      
   catch: 
      print("Timeout!", time[real]()-st);      
   end try;  
end do;  
end proc:

################ proc testZeroRadical1
testZeroRadical1 := proc(ex, m:=-1, n:=-1)
local i,st,ZR,tm,tn;  
tm:=m;tn:=n;
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do  
   print("###");    
   print("num:", i);      
   try 
      st := time[real]():
      timelimit[real](3600, ZeroRadical1(op(ex[i])));      
   catch: 
      print("Timeout!", time[real]()-st);      
   end try;  
end do;  
end proc:

################ proc testMapleSfNormal
testMapleSfNormal := proc(ex, m:=-1, n:=-1)
local i,st,tm,tn;
tm:=m;tn:=n;
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do 
   print("###");     
   print("num:", i);      
   try 
      st := time[real]():
      timelimit[real](3600, MapleSfNormal(op(ex[i])));      
   catch: 
      print("Timeout!", time[real]()-st);      
   end try;  
end do;  
end proc:

################ proc testMapleRadical
testMapleRadical := proc(ex, m:=-1, n:=-1, expect:={}) 
local i, temp, ans, st,tm,tn;
tm:=m;tn:=n; 
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do 
   print("###");
   print("num:", i);
   if i in expect then
      print("Timeout!",4000);
   else
      try 
         st := time[real]():
         timelimit[real](3600, print(time[real](Radical(PolynomialIdeal(op(ex[i][1])))))); 
      catch: 
         print("Timeout!", time[real]()-st); 
      end try;
   end if; 
end do; 
end proc:

################ proc testMapleIsolate
testMapleIsolate := proc(ex, digits, m:=-1, n:=-1)
local i,st,tm,tn;
tm:=m;tn:=n;
if m<1 then
   tm:=1;
end if;
if n<1 then
  tn:=nops(ex);
end if;
for i from tm to tn do    
   print("###");   
   print("num:", i);      
   try 
      st := time[real]():
      timelimit[real](3600, print(time[real](Isolate(op(ex[i]), digits, output=interval))));      
      # timelimit[real](600, print(time[real](Isolate(da1[i][1], Reverse(da1[i][2]), digits, output=interval))));     
   catch: 
      print("Timeout!", time[real]()-st);      
   end try;  
end do;  
end proc:

# ################
# testans := proc(m, n)
# local i, temp, ans;  
# ans := [];
# for i from m to n do  
#    print("cm:", i);     
#    temp := RealRoot(op(cm[i]), 1);
#    ans  := [op(ans), [i, temp]];
# end do;  
# save ans, "C:/Users/zhaot/Documents/GitHub/FGT_realroot/RSD/RSD_code/cm_ans1.mpl";
# end proc: