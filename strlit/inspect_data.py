#!/usr/bin/env python3
# usage: inspect_data.py FILE.lean  -- print length and character histogram of the first string literal after 'def data'
import re, sys, collections
s = open(sys.argv[1], encoding='utf-8').read()
i = s.index('def data')
j = s.index('"', i)
k = j + 1
out = []
while True:
    c = s[k]
    if c == '\\':
        out.append(s[k:k+2]); k += 2; continue
    if c == '"': break
    out.append(c); k += 1
d = ''.join(out)
print('raw literal chars (escapes counted as 2):', len(d))
print(collections.Counter(out).most_common(60))
print('head:', repr(d[:300]))
print('non-ascii:', sum(1 for c in d if ord(c) > 127))
