# SfStrongTriDec
SfStrongTriDec is short for square-free strong triangular decomposition (SFSTD).
We propose an algorithm for SFSTD of zero-dimensional polynomial systems in our paper.
## Code
All code is in "SFSTD.mpl".
- The procedure "PolylistToNormal" is used for computing strong triangular decomposition (STD) of zero-dimensional polynomial systems.
- The procedure "PolylistToSfNormal" is used for computing SFSTD of zero-dimensional polynomial systems.
### Dependency
[Maple 2021](https://www.maplesoft.com.cn/products/maple/professional/index.shtml)
### Using
```maple
read ".../SFSTD.mpl";
PolylistToNormal(sys, vars);
PolylistToSfNormal(sys, vars);
```
## Examples
- Testing examples in "cm.mpl" are from [^1].
- Testing examples in "wangzero.mpl" are from [^2].
- Testing examples in "xia2006.mpl" are from [^3].
- Testing examples in "database1.mpl" and "database2.mpl" are from [^4].

Total 151 testing examples are also in "allbench.wls". 

[^1]:=https://doi.org/10.1007/978-3-662-43799-5_4
[^2]:=https://doi.org/10.1016/S0378-4754(96)00008-0
[^3]:=https://doi.org/10.1016/j.camwa.2006.06.003
[^4]:=http://homepages.math.uic.edu/~jan/demo.html


## Experimental Results
We present our experimental results in the sheet "allbench.csv".
Note that the column "Algorithm 3" and the column "mp-rc" record the time for triangular decomposition (followed by the numbers of components in parenthesis) by Algorithm 3 and the method mp-rc respectively.
All tests were conducted on 16-Core Intel Core i7-12900KF@3.20GHz
with 128GB of memory and Windows 11.