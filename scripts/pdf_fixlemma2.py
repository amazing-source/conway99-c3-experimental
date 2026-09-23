# Mise en forme : liste des énoncés Lean (évite les débordements) et formulation de la fin du lemme 7.
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:90])
    s = s.replace(a, b)


rep(r"""ainsi que le voisin commun $c$ de $x$ et $a$ (point~1) ; alors $a$ a trois voisins fixes $x,y,c$, contradiction. Donc $F$ est
contenu dans $x$ et ses deux voisins fixes : $|F|\le3$. \qedhere""",
    r"""ainsi que le voisin commun $c$ de $x$ et $a$ (point~1) ; alors $a$ a trois voisins fixes $x,y,c$, contradiction. Donc tout point
fixe est $x$ ou l'un de ses deux voisins fixes : $|F|\le3$. \qedhere""")

rep(r"""\item \textbf{Vérification formelle.} Tous les énoncés sont vérifiés en Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans
\texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement régulier (\texttt{SimpleGraph.IsSRGWith}).
L'énoncé final est \texttt{C3.no\_order3} : tout automorphisme $\sigma$ tel que $\sigma^3=1$ est l'identité (corollaire~\ref{cor:tout},
sans \cite{MM04}). Les étapes sont \texttt{C3.no\_free\_order3} (théorème~\ref{thm:libre}), \texttt{C3.no\_triangle\_order3}
(proposition~\ref{prop:triangle} ; le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes),
ainsi que les versions matricielles \texttt{C3.no\_pair} (théorème~\ref{thm:matrices}) et \texttt{C3.Tri.no\_triangle\_pair}
(§4). Tous ne dépendent que des axiomes standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}, et
n'emploient que des définitions de Mathlib : un relecteur n'a à contrôler que l'énoncé de \texttt{C3.no\_order3}. Sources :
dossier \texttt{c3formal/}.""",
    r"""\item \textbf{Vérification formelle.} Tous les énoncés sont vérifiés en Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans
\texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement régulier (\texttt{SimpleGraph.IsSRGWith}) :
\begin{itemize}[leftmargin=1.2em,nosep]
\item \texttt{C3.no\_order3} : tout automorphisme $\sigma$ tel que $\sigma^3=1$ est l'identité (corollaire~\ref{cor:tout},
sans \cite{MM04}) ;
\item \texttt{C3.no\_free\_order3} (théorème~\ref{thm:libre}) ;
\item \texttt{C3.no\_triangle\_order3} (proposition~\ref{prop:triangle} ; le triangle y est démontré) ;
\item \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes) ;
\item \texttt{C3.no\_pair} (théorème~\ref{thm:matrices}) et \texttt{C3.Tri.no\_triangle\_pair} (§4), les versions matricielles.
\end{itemize}
Tous ne dépendent que des axiomes standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}, et n'emploient que
des définitions de Mathlib : un relecteur n'a à contrôler que l'énoncé de \texttt{C3.no\_order3}. Sources : dossier
\texttt{c3formal/}.""")

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
