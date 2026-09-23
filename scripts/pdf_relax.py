# Annule le resserrement « 4 pages » de pdf/preuve_c3.tex (pas de budget de pages), 2026-09-23.
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80])
    s = s.replace(a, b)


rep(r"\usepackage[hmargin=2.0cm,vmargin=1.6cm]{geometry}", r"\usepackage[margin=2.5cm]{geometry}")
rep(r"\setlength{\parskip}{2pt}", r"\setlength{\parskip}{3pt}")
rep("\\section{Remarques}\n\\small\n", "\\section{Remarques}\n")
rep("{\\footnotesize\n\\begin{thebibliography}", "{\\small\n\\begin{thebibliography}")
rep("\\bibitem[Br]{Br} A.\\,E.~Brouwer, \\emph{Parameters of strongly regular graphs},\n"
    "\\url{https://aeb.win.tue.nl/graphs/srg/srgtab.html}.",
    "\\bibitem[Br]{Br} A.\\,E.~Brouwer, \\emph{Parameters of strongly regular graphs}, tables en ligne,\n"
    "\\url{https://aeb.win.tue.nl/graphs/srg/srgtab.html}.")

rep(r"""La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur.""",
    r"""La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur ; le théorème~1 et la
proposition~2 sont vérifiés en Lean~4, à partir de la définition d'un graphe fortement régulier.""")

rep(r"""(\texttt{SimpleGraph.IsSRGWith}) : \texttt{C3.no\_free\_order3}, \texttt{C3.no\_triangle\_order3} (exactement trois points fixes ;
le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes), qui ne dépendent que des axiomes
standard de Lean. Un relecteur n'a à contrôler que ces énoncés. Seul \cite{MM04} (corollaire~\ref{cor:tout}) n'est pas formalisé.""",
    r"""(\texttt{SimpleGraph.IsSRGWith}) : \texttt{C3.no\_free\_order3}, \texttt{C3.no\_triangle\_order3} (exactement trois points fixes ;
le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes). Ils ne dépendent que des axiomes
standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}, et n'emploient que des définitions de Mathlib : un
relecteur n'a à contrôler que ces énoncés. Les versions matricielles (théorème~\ref{thm:matrices} et §4) sont aussi vérifiées
(\texttt{C3.no\_pair}, \texttt{C3.Tri.no\_triangle\_pair}). Seul le théorème de Makhnev--Minakova (corollaire~\ref{cor:tout})
n'est pas formalisé. Sources : dossier \texttt{c3formal/}.""")

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
