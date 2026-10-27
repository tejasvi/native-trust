| batch | toolchain | content | chars | op | method | bytes | D | time s | peak GB | (peak-base)/D KB | rc |
|---|---|---|---|---|---|---|---|---|---|---|---|
| b1 | v4.34.0-rc2 | a | 1000 | ubs | dk | 1000 | 1000 | 0.49 | 0.53 | 61.8 | rc=0 |
| b1 | v4.34.0-rc2 | dw | 1000 | ubs | dk | 1000 | 494506 | 21.19 | 4.63 | 8.4 | rc=0 |
| b1 | v4.34.0-rc2 | dw | 250 | ubs | dk | 250 | 30557 | 1.61 | 0.74 | 8.6 | rc=0 |
| b1 | v4.34.0-rc2 | dw | 500 | ubs | dk | 500 | 123311 | 5.07 | 1.52 | 8.5 | rc=0 |
| b1 | v4.34.0-rc2 | rep8 | 1000 | ubs | dk | 1000 | 7971 | 0.7 | 0.59 | 14.7 | rc=0 |
| b1 | v4.34.0-rc2 | rep8 | 250 | ubs | dk | 250 | 1971 | 0.27 | 0.51 | 17.0 | rc=0 |
| b1 | v4.34.0-rc2 | rep8 | 500 | ubs | dk | 500 | 3971 | 0.47 | 0.53 | 15.0 | rc=0 |
| b1 | v4.34.0-rc2 | rnd | 1000 | ubs | dk | 1000 | 498517 | 21.26 | 4.66 | 8.4 | rc=0 |
| full | v4.34.0-rc2 | dw | 7824 | ubs | dk(no maxRecDepth) | 7824 | 29931381 | 1.27 | 0.72 | 0.0 | rc=1 |
| full | v4.34.0-rc2 | dw | 7824 | ubs | dk | 7824 | 29931381 | 61.67 | 20.30 | 0.7 | rc=134 |
| full | v4.34.0-rc2 | dw_7824 | ubs | dk | nomrd (default lean flags + default ulimit -s) |  |  | 1.27 | 0.74 |  | rc=1 |
| m1 | v4.34.0-rc2 | per64 | 2000 | ubs | dk | 2000 | 125924 | 6.14 | 1.62 | 9.1 | rc=0 |
| m1 | v4.34.0-rc2 | per16 | 2000 | ubs | dk | 2000 | 31875 | 2.15 | 0.83 | 11.3 | rc=0 |
| m1 | v4.34.0-rc2 | rep8 | 2000 | ubs | dk | 2000 | 15971 | 1.24 | 0.70 | 14.4 | rc=0 |
| m1 | v4.34.0-rc2 | rep8 | 4000 | ubs | dk | 4000 | 31971 | 3.05 | 0.93 | 14.5 | rc=0 |
| m1 | v4.34.0-rc2 | per256 | 2000 | ubs | dk | 2000 | 478992 | 22.26 | 4.55 | 8.5 | rc=0 |
| m1 | v4.34.0-rc2 | a | 4000 | ubs | dk | 4000 | 4000 | 1.48 | 0.70 | 56.4 | rc=0 |
| m1 | v4.34.0-rc2 | a | 8000 | ubs | dk | 8000 | 8000 | 3.09 | 0.92 | 56.5 | rc=0 |
| m1 | v4.34.0-rc2 | per64 | 1000 | ubs | dk | 1000 | 61924 | 4.1 | 1.03 | 9.0 | rc=0 |
| m1 | v4.34.0-rc2 | per256 | 1000 | ubs | dk | 1000 | 222992 | 10.79 | 2.37 | 8.5 | rc=0 |
| m1 | v4.34.0-rc2 | rnd | 250 | ubs | dk | 250 | 31019 | 1.65 | 0.74 | 8.6 | rc=0 |
| m1 | v4.34.0-rc2 | rnd | 500 | ubs | dk | 500 | 124385 | 5.04 | 1.53 | 8.5 | rc=0 |
| m1 | v4.34.0-rc2 | rep8 | 8000 | ubs | dk | 8000 | 63971 | 51.58 | 1.40 | 14.5 | rc=0 |
| m1 | v4.34.0-rc2 | dig | 1000 | ubs | dk | 1000 | 498178 | 20.57 | 4.66 | 8.4 | rc=0 |
| m1 | v4.34.0-rc2 | per1024 | 2000 | ubs | dk | 2000 | 1522184 | 69.98 | 13.27 | 8.4 | rc=0 |
| m1 | v4.34.0-rc2 | sp | 1000 | ubs | dk | 1000 | 1000 | 0.46 | 0.53 | 60.9 | rc=0 |
| m1 | v4.34.0-rc2 | nl | 1000 | ubs | dk | 1000 | 1000 | 0.36 | 0.53 | 61.7 | rc=0 |
| m1 | v4.34.0-rc2 | na2 | 250 | ubs | dk | 500 | 123674 | 5.63 | 1.52 | 8.5 | rc=0 |
| m1 | v4.34.0-rc2 | dw | 2000 | ubs | dk | 2000 | 1901134 | 84.31 | 16.37 | 8.4 | rc=0 |
| m1 | v4.34.0-rc2 | bin | 1000 | ubs | dk | 1000 | 491518 | 21.23 | 4.61 | 8.4 | rc=0 |
| m1 | v4.34.0-rc2 | punct | 1000 | ubs | dk | 1000 | 499049 | 19.27 | 4.67 | 8.4 | rc=0 |
| m1 | v4.34.0-rc2 | na3 | 250 | ubs | dk | 738 | 269206 | 12.96 | 2.74 | 8.4 | rc=0 |
| m1 | v4.34.0-rc2 | na4 | 250 | ubs | dk | 1000 | 492118 | 19.0 | 4.62 | 8.4 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | eq | dk | 500 | 123311 | 5.88 | 1.53 | 8.6 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | eqv | dk | 500 | 123311 | 5.92 | 1.53 | 8.6 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | dd | dk | 500 | 123311 | 6.14 | 1.53 | 8.6 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | tol | dk | 500 | 123311 | 18.4 | 4.65 | 33.9 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 500 | eq | dk | 500 | 3971 | 0.57 | 0.54 | 17.6 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 500 | eqv | dk | 500 | 3971 | 0.44 | 0.54 | 17.6 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 500 | dd | dk | 500 | 3971 | 0.58 | 0.54 | 17.8 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | len | dk | 500 | 123311 | 21.54 | 4.65 | 33.9 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 500 | len | dk | 500 | 3971 | 16.43 | 3.66 | 803.7 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | ubsN | dk | 500 | 123311 | 5.4 | 1.52 | 8.5 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 500 | tol | dk | 500 | 3971 | 14.99 | 3.67 | 803.9 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 2000 | eqv | trfl | 2000 | 1901134 | 0.15 | 0.47 | 0.0 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 2000 | dd | trfl | 2000 | 1901134 | 0.21 | 0.47 | -0.0 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | ubsN | rfl | 500 | 123311 | 8.99 | 1.52 | 8.5 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | ubsN | nde | 500 | 123311 | 5.9 | 1.52 | 8.5 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 1000 | sofl | dk | 1000 | 7971 | 1.08 | 0.61 | 17.1 | rc=0 |
| m2 | v4.34.0-rc2 | rnd | 1000 | fmlen | dk | 1000 | 498517 | 0.61 | 0.53 | 0.1 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 500 | ubsN | trfl | 500 | 123311 | 16.77 | 1.52 | 8.5 | rc=0 |
| m2 | v4.34.0-rc2 | rnd | 1000 | u8arr | dk | 1000 | 498517 | 0.61 | 0.51 | 0.1 | rc=0 |
| m2 | v4.34.0-rc2 | rnd | 1000 | sofl | dk | 1000 | 498517 | 22.52 | 4.68 | 8.4 | rc=0 |
| m2 | v4.34.0-rc2 | rep8 | 1000 | fmtba | dk | 1000 | 7971 | 1.07 | 0.61 | 17.1 | rc=0 |
| m2 | v4.34.0-rc2 | rnd | 1000 | fmtba | dk | 1000 | 498517 | 22.92 | 4.68 | 8.4 | rc=0 |
| m2 | v4.34.0-rc2 | rnd | 1000 | u8tba | dk | 1000 | 498517 | 24.03 | 4.66 | 8.4 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 250 | len | dk | 250 | 30557 | 5.18 | 1.53 | 34.7 | rc=0 |
| m2 | v4.34.0-rc2 | dw | 250 | tol | dk | 250 | 30557 | 5.46 | 1.53 | 34.7 | rc=0 |
| m2 | v4.34.0-rc2 | rnd | 1000 | u8push | dk | 1000 | 498517 | 23.34 | 4.66 | 8.4 | rc=0 |
| m3 | v4.35.0 | per256 | 2000 | ubs | dk | 2000 | 478992 | 20.59 | 4.46 | 8.3 | rc=0 |
| m3 | v4.35.0 | dw | 1000 | ubs | dk | 1000 | 494506 | 21.74 | 4.54 | 8.2 | rc=0 |
| m3 | v4.35.0 | dw | 250 | ubs | dk | 250 | 30557 | 1.5 | 0.73 | 8.3 | rc=0 |
| m3 | v4.35.0 | rep8 | 1000 | ubs | dk | 1000 | 7971 | 0.8 | 0.58 | 13.6 | rc=0 |
| m3 | v4.35.0 | rep8 | 4000 | ubs | dk | 4000 | 31971 | 3.5 | 0.92 | 13.9 | rc=0 |
| m3 | v4.35.0 | dw | 500 | ubs | dk | 500 | 123311 | 5.02 | 1.49 | 8.3 | rc=0 |
| m3 | v4.35.0 | a | 8000 | ubs | dk | 8000 | 8000 | 2.66 | 0.91 | 54.5 | rc=0 |
| m3 | v4.35.0 | dw | 250 | len | dk | 250 | 30557 | 4.46 | 1.50 | 33.7 | rc=0 |
| m3 | v4.35.0 | rep8 | 500 | len | dk | 500 | 3971 | 13.54 | 3.61 | 790.1 | rc=0 |
| m3 | v4.35.0 | rep8 | 8000 | ubs | dk | 8000 | 63971 | 45.19 | 1.37 | 14.0 | rc=0 |
| m3 | v4.35.0 | dw | 500 | len | dk | 500 | 123311 | 18.73 | 4.57 | 33.2 | rc=0 |
| m3 | v4.35.0 | rnd | 1000 | fmlen | dk | 1000 | 498517 | 0.56 | 0.52 | 0.1 | rc=0 |
| m3 | v4.35.0 | dw | 500 | ubsN | trfl | 500 | 123311 | 15.86 | 1.49 | 8.3 | rc=0 |
| m3 | v4.35.0 | dw | 2000 | eqv | trfl | 2000 | 1901134 | 0.18 | 0.46 | -0.0 | rc=0 |
| m3 | v4.35.0 | rnd | 1000 | u8push | dk | 1000 | 498517 | 22.16 | 4.57 | 8.2 | rc=0 |
| m3 | v4.35.0 | rnd | 1000 | sofl | dk | 1000 | 498517 | 22.27 | 4.59 | 8.3 | rc=0 |
| m3 | v4.35.0 | dw | 2000 | ubs | dk | 2000 | 1901134 | 81.24 | 16.04 | 8.2 | rc=0 |
| m3 | v4.35.0 | na4 | 250 | ubs | dk | 1000 | 492118 | 20.72 | 4.52 | 8.2 | rc=0 |
| m4 | v4.34.0-rc2 | a | 16000 | ubs | dk | 16000 | 16000 | 5.44 | 1.38 | 56.5 | rc=0 |
| m4 | v4.34.0-rc2 | per16 | 4000 | ubs | dk | 4000 | 63875 | 4.21 | 1.20 | 11.4 | rc=0 |
| m4 | v4.34.0-rc2 | per16 | 8000 | ubs | dk | 8000 | 127875 | 7.61 | 1.93 | 11.4 | rc=0 |
| m4 | v4.34.0-rc2 | rep8 | 6000 | ubs | dk | 6000 | 47971 | 17.37 | 1.17 | 14.5 | rc=0 |
| m4 | v4.34.0-rc2 | per2 | 8000 | ubs | dk | 8000 | 15999 | 3.13 | 0.99 | 32.4 | rc=0 |
| m4 | v4.34.0-rc2 | per4 | 8000 | ubs | dk | 8000 | 31994 | 4.06 | 1.13 | 20.5 | rc=0 |
| m4 | v4.34.0-rc2 | per8 | 8000 | ubs | dk | 8000 | 63970 | 4.94 | 1.39 | 14.3 | rc=0 |
| m4 | v4.34.0-rc2 | rep8 | 8000 | ubs | dk | 8000 | 63971 | 55.05 | 1.40 | 14.4 | rc=0 |
| m4 | v4.34.0-rc2 | rep8 | 12000 | ubs | dk | 12000 | 95971 | 264.65 | 1.86 | 14.5 | rc=0 |
| m5 | v4.34.0-rc2 | rep8 | 1000 | u8push | dk | 1000 | 7971 | 1.1 | 0.59 | 15.3 | rc=0 |
| m5 | v4.34.0-rc2 | B-01234567 | 8000 | ubs | dk | 8000 | 63972 | 4.53 | 1.39 | 14.3 | rc=0 |
| m5 | v4.34.0-rc2 | dw | 1000 | len | dk | 1000 | 494506 | 73.42 | 17.03 | 33.5 | rc=0 |
| m5 | v4.34.0-rc2 | dw | 4000 | ubs | dk | 4000 | 7740835 | 73.83 | 20.34 | 2.6 | rc=134 |
| m5 | v4.34.0-rc2 | cnt | 2000 | ubs | dk | 2000 | 1995763 | 79.16 | 17.14 | 8.4 | rc=0 |
| m6 | v4.34.0-rc2 | B-613~201_ | 8000 | ubs | dk | 8000 | 63971 | 4.29 | 1.39 | 14.3 | rc=0 |
| m6 | v4.34.0-rc2 | B-613~2000 | 8000 | ubs | dk | 8000 | 63969 | 5.25 | 1.39 | 14.3 | rc=0 |
| m6 | v4.34.0-rc2 | B-61302000 | 8000 | ubs | dk | 8000 | 63968 | 4.77 | 1.39 | 14.3 | rc=0 |
| m6 | v4.34.0-rc2 | B-abcdefgh | 8000 | ubs | dk | 8000 | 63972 | 4.91 | 1.39 | 14.3 | rc=0 |
| m6 | v4.34.0-rc2 | B-aaaaaaab | 8000 | ubs | dk | 8000 | 63951 | 4.33 | 1.39 | 14.4 | rc=0 |
| m6 | v4.34.0-rc2 | B-613~200_ | 7000 | ubs | dk | 7000 | 55971 | 27.06 | 1.28 | 14.5 | rc=0 |
| m6 | v4.34.0-rc2 | B-613~200_ | 8000 | ubs | dk | 8000 | 63971 | 47.38 | 1.39 | 14.4 | rc=0 |
| m6 | v4.34.0-rc2 | B-200_613~ | 8000 | ubs | dk | 8000 | 63971 | 47.46 | 1.40 | 14.4 | rc=0 |
| rd | v4.34.0-rc2 | cnt | 250 | ubs | dk(no maxRecDepth) | 250 | 30976 | 1.32 | 0.74 | 8.7 | rc=0 |
| rd | v4.34.0-rc2 | cnt | 500 | ubs | dk(no maxRecDepth) | 500 | 124209 | 5.35 | 1.53 | 8.5 | rc=0 |
| rd | v4.34.0-rc2 | cnt | 1000 | ubs | dk(no maxRecDepth) | 1000 | 498060 | 19.2 | 4.66 | 8.4 | rc=0 |
| rd2 | v4.34.0-rc2 | cnt | 1000 | ubs | dk | 1000 | 498060 | 19.71 | 4.66 | 8.4 | rc=0 |
| rd2 | v4.34.0-rc2 | cnt | 1000 | ubs | dk(no maxRecDepth) | 1000 | 498060 | 21.02 | 4.66 | 8.4 | rc=0 |
| repro | v4.34.0-rc2 | rep8 | 1000 | ubs | dk | 1000 | 7971 | 0.81 | 0.59 | 14.6 | rc=0 |
| repro | v4.34.0-rc2 | cnt | 1000 | ubs | dk | 1000 | 498060 | 19.09 | 4.66 | 8.4 | rc=0 |
| repro | v4.34.0-rc2 | cnt | 1000 | u8push | dk | 1000 | 498060 | 20.62 | 4.66 | 8.4 | rc=0 |
| repro | v4.35.0 | rep8 | 1000 | ubs | dk | 1000 | 7971 | 0.71 | 0.58 | 13.6 | rc=0 |
| repro | v4.35.0 | cnt | 1000 | ubs | dk | 1000 | 498060 | 18.92 | 4.57 | 8.2 | rc=0 |
| repro | v4.35.0 | cnt | 1000 | u8push | dk | 1000 | 498060 | 19.71 | 4.57 | 8.2 | rc=0 |
| thr | v4.34.0-rc2 | dw | 2500 | ubs | dk(no maxRecDepth) |  |  | 0.63 | 0.57 |  | rc=1 |
| thr | v4.34.0-rc2 | dw | 2000 | ubs | dk(no maxRecDepth) | 2000 | 1901134 | 0.72 | 0.55 | 0.0 | rc=1 |
| thr | v4.34.0-rc2 | dw | 3000 | ubs | dk(no maxRecDepth) |  |  | 0.9 | 0.59 |  | rc=1 |
| thr | v4.34.0-rc2 | dw | 3500 | ubs | dk(no maxRecDepth) |  |  | 1.0 | 0.61 |  | rc=1 |
| thr | v4.34.0-rc2 | dw | 4000 | ubs | dk(no maxRecDepth) | 4000 | 7740835 | 1.11 | 0.63 | 0.0 | rc=1 |
| thr | v4.34.0-rc2 | dw | 5000 | ubs | dk(no maxRecDepth) |  |  | 0.94 | 0.65 |  | rc=1 |
| thr | v4.34.0-rc2 | dw | 6000 | ubs | dk(no maxRecDepth) |  |  | 1.04 | 0.68 |  | rc=1 |
| thr | v4.34.0-rc2 | dw | 1500 | ubs | dk(no maxRecDepth) |  |  | 20.03 | 6.48 |  | rc=124 |
| thr2 | v4.34.0-rc2 | dw | 1750 | ubs | dk(no maxRecDepth) |  |  | 0.51 | 0.54 |  | rc=1 |
| thr2 | v4.34.0-rc2 | a | 2000 | ubs | dk(no maxRecDepth) |  |  | 0.71 | 0.55 |  | rc=1 |
| thr2 | v4.34.0-rc2 | rep8 | 4000 | ubs | dk(no maxRecDepth) | 4000 | 31971 | 1.08 | 0.62 | 4.6 | rc=1 |
| thr2 | v4.34.0-rc2 | a | 8000 | ubs | dk(no maxRecDepth) | 8000 | 8000 | 1.32 | 0.75 | 34.1 | rc=1 |

fit over 64 runs (utf8ByteSize, decide +kernel, rc=0): peak_KB - 472744 = 48.6 KB * bytes + 8.27 KB * D
max |predicted - measured| / measured = 0.021
  bytes=  1000 D=    1000 measured=  0.53 GB predicted=  0.53 GB
  bytes=  1000 D=    1000 measured=  0.53 GB predicted=  0.53 GB
  bytes=  1000 D=    1000 measured=  0.53 GB predicted=  0.53 GB
  bytes=   250 D=    1971 measured=  0.51 GB predicted=  0.50 GB
  bytes=   500 D=    3971 measured=  0.53 GB predicted=  0.53 GB
  bytes=  4000 D=    4000 measured=  0.70 GB predicted=  0.70 GB
  bytes=  1000 D=    7971 measured=  0.59 GB predicted=  0.59 GB
  bytes=  1000 D=    7971 measured=  0.58 GB predicted=  0.59 GB
  bytes=  1000 D=    7971 measured=  0.59 GB predicted=  0.59 GB
  bytes=  1000 D=    7971 measured=  0.58 GB predicted=  0.59 GB
  bytes=  8000 D=    8000 measured=  0.92 GB predicted=  0.93 GB
  bytes=  8000 D=    8000 measured=  0.91 GB predicted=  0.93 GB
  bytes=  2000 D=   15971 measured=  0.70 GB predicted=  0.70 GB
  bytes=  8000 D=   15999 measured=  0.99 GB predicted=  0.99 GB
  bytes= 16000 D=   16000 measured=  1.38 GB predicted=  1.38 GB
  bytes=   250 D=   30557 measured=  0.74 GB predicted=  0.74 GB
  bytes=   250 D=   30557 measured=  0.73 GB predicted=  0.74 GB
  bytes=   250 D=   31019 measured=  0.74 GB predicted=  0.74 GB
  bytes=  2000 D=   31875 measured=  0.83 GB predicted=  0.83 GB
  bytes=  4000 D=   31971 measured=  0.93 GB predicted=  0.93 GB
  bytes=  4000 D=   31971 measured=  0.92 GB predicted=  0.93 GB
  bytes=  8000 D=   31994 measured=  1.13 GB predicted=  1.13 GB
  bytes=  6000 D=   47971 measured=  1.17 GB predicted=  1.16 GB
  bytes=  7000 D=   55971 measured=  1.28 GB predicted=  1.28 GB
  bytes=  1000 D=   61924 measured=  1.03 GB predicted=  1.03 GB
  bytes=  4000 D=   63875 measured=  1.20 GB predicted=  1.20 GB
  bytes=  8000 D=   63951 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63968 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63969 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63970 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63971 measured=  1.40 GB predicted=  1.39 GB
  bytes=  8000 D=   63971 measured=  1.37 GB predicted=  1.39 GB
  bytes=  8000 D=   63971 measured=  1.40 GB predicted=  1.39 GB
  bytes=  8000 D=   63971 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63971 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63971 measured=  1.40 GB predicted=  1.39 GB
  bytes=  8000 D=   63972 measured=  1.39 GB predicted=  1.39 GB
  bytes=  8000 D=   63972 measured=  1.39 GB predicted=  1.39 GB
  bytes= 12000 D=   95971 measured=  1.86 GB predicted=  1.85 GB
  bytes=   500 D=  123311 measured=  1.52 GB predicted=  1.52 GB
  bytes=   500 D=  123311 measured=  1.49 GB predicted=  1.52 GB
  bytes=   500 D=  123674 measured=  1.52 GB predicted=  1.52 GB
  bytes=   500 D=  124385 measured=  1.53 GB predicted=  1.53 GB
  bytes=  2000 D=  125924 measured=  1.62 GB predicted=  1.61 GB
  bytes=  8000 D=  127875 measured=  1.93 GB predicted=  1.92 GB
  bytes=  1000 D=  222992 measured=  2.37 GB predicted=  2.36 GB
  bytes=   738 D=  269206 measured=  2.74 GB predicted=  2.73 GB
  bytes=  2000 D=  478992 measured=  4.55 GB predicted=  4.53 GB
  bytes=  2000 D=  478992 measured=  4.46 GB predicted=  4.53 GB
  bytes=  1000 D=  491518 measured=  4.61 GB predicted=  4.58 GB
  bytes=  1000 D=  492118 measured=  4.62 GB predicted=  4.59 GB
  bytes=  1000 D=  492118 measured=  4.52 GB predicted=  4.59 GB
  bytes=  1000 D=  494506 measured=  4.63 GB predicted=  4.61 GB
  bytes=  1000 D=  494506 measured=  4.54 GB predicted=  4.61 GB
  bytes=  1000 D=  498060 measured=  4.66 GB predicted=  4.64 GB
  bytes=  1000 D=  498060 measured=  4.66 GB predicted=  4.64 GB
  bytes=  1000 D=  498060 measured=  4.57 GB predicted=  4.64 GB
  bytes=  1000 D=  498178 measured=  4.66 GB predicted=  4.64 GB
  bytes=  1000 D=  498517 measured=  4.66 GB predicted=  4.64 GB
  bytes=  1000 D=  499049 measured=  4.67 GB predicted=  4.65 GB
  bytes=  2000 D= 1522184 measured= 13.27 GB predicted= 13.15 GB
  bytes=  2000 D= 1901134 measured= 16.37 GB predicted= 16.28 GB
  bytes=  2000 D= 1901134 measured= 16.04 GB predicted= 16.28 GB
  bytes=  2000 D= 1995763 measured= 17.14 GB predicted= 17.07 GB
