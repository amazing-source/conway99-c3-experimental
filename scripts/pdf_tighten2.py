# Réduit la taille des remarques et de la bibliographie (pdf/preuve_c3.tex), 2026-09-23.
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80])
    s = s.replace(a, b)


rep("\\section{Remarques}\n", "\\section{Remarques}\n\\small\n")
rep("{\\small\n\\begin{thebibliography}", "{\\footnotesize\n\\begin{thebibliography}")
rep("\\bibitem[Br]{Br} A.\\,E.~Brouwer, \\emph{Parameters of strongly regular graphs}, tables en ligne,\n"
    "\\url{https://aeb.win.tue.nl/graphs/srg/srgtab.html}.",
    "\\bibitem[Br]{Br} A.\\,E.~Brouwer, \\emph{Parameters of strongly regular graphs},\n"
    "\\url{https://aeb.win.tue.nl/graphs/srg/srgtab.html}.")

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
