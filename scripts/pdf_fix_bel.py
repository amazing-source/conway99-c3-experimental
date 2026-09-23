# Répare le caractère BEL introduit par sed dans pdf/preuve_c3.tex (\a interprété par sed).
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()
bad = "\\texttt{SimpleGraph.\x07llowbreak IsSRGWith}"
good = "\\texttt{SimpleGraph.\\allowbreak IsSRGWith}"
assert s.count(bad) == 1, s.count(bad)
s = s.replace(bad, good)
assert "\x07" not in s
io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
