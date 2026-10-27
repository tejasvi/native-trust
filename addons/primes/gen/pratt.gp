\\ Pratt certificate generator (post-order: factors before their parent).
\\ Output lines: NODE p a q1 e1 q2 e2 ...
default(parisizemax, 4000000000);
seen = Map();
pratt(p) = {
  my(f, a, ok, s);
  if (p == 2, return);
  if (mapisdefined(seen, p), return);
  f = factor(p - 1);
  for (i = 1, #f~, if (f[i,1] > 2, pratt(f[i,1])));
  a = 2;
  while (1,
    if (Mod(a, p)^(p-1) == 1,
      ok = 1;
      for (i = 1, #f~, if (Mod(a, p)^((p-1)/f[i,1]) == 1, ok = 0; break));
      if (ok, break));
    a++);
  mapput(seen, p, 1);
  s = Str("NODE ", p, " ", a);
  for (i = 1, #f~, s = Str(s, " ", f[i,1], " ", f[i,2]));
  print(s);
}
