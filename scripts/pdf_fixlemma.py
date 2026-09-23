# Ajoute le lemme des points fixes (preuve élémentaire, remplace Makhnev–Minakova) à pdf/preuve_c3.tex.
# 2026-09-23.
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:90])
    s = s.replace(a, b)


rep(r"""\small Le théorème~1 et la proposition~2 sont vérifiés en Lean~4 / Mathlib (voir §5).}""",
    r"""\small Tous les énoncés sont vérifiés en Lean~4 / Mathlib (voir §6).}""")

rep(r"""observé que les coordonnées des points fixes sont divisibles par~3.
Avec un théorème de Makhnev et Minakova, il en résulte que $\Gamma$ n'a aucun automorphisme d'ordre~3.
La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur ; le théorème~1 et la
proposition~2 sont vérifiés en Lean~4, à partir de la définition d'un graphe fortement régulier.""",
    r"""observé que les coordonnées des points fixes sont divisibles par~3.
Un comptage élémentaire (qui redémontre un résultat de Makhnev et Minakova) montre qu'un automorphisme d'ordre~3 a au plus trois
points fixes ; il en résulte que $\Gamma$ n'a aucun automorphisme d'ordre~3.
La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur ; elle est entièrement
vérifiée en Lean~4, à partir de la définition d'un graphe fortement régulier, sans aucune entrée extérieure.""")

rep(r"""D'après Makhnev et Minakova \cite{MM04}, les points fixes d'un automorphisme d'ordre~3 forment l'ensemble vide ou un triangle.
On conclut par le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle}. (Sans \cite{MM04} : le nombre de points fixes
est $\equiv 99\equiv0\pmod3$, donc ces deux énoncés excluent déjà tout automorphisme d'ordre~3 ayant au plus trois points fixes ; le cas avec points fixes est aussi exclu, par une recherche sur
ordinateur, dans \cite{B09,BL11}.)""",
    r"""Soit $g\ne1$ avec $g^3=1$. Par le lemme~\ref{lem:fix} (§5), $g$ a au plus trois points fixes. Leur nombre est
$\equiv 99\equiv0\pmod3$, car les autres sommets forment des orbites de taille~3 : il vaut donc $0$ ou $3$, et l'on conclut par le
théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle}. (Le lemme~\ref{lem:fix} est dû à Makhnev et Minakova \cite{MM04},
sous la forme « les points fixes forment l'ensemble vide ou un triangle » ; le cas avec points fixes est aussi exclu, par une
recherche sur ordinateur, dans \cite{B09,BL11}.)""")

new_sec = r"""%====================================================================
\section{Les points fixes (corollaire~\ref{cor:tout})}

\begin{lemma}\label{lem:fix}
Soit $g\ne1$ un automorphisme de $\Gamma$ tel que $g^3=1$. Alors $g$ a au plus trois points fixes.
\end{lemma}
\begin{proof}
Soit $F$ l'ensemble des points fixes et, pour $x\in F$, $n_x$ le nombre de voisins fixes de $x$.
\begin{enumerate}[leftmargin=*,nosep]
\item \emph{Fermeture.} Un sommet $v$ adjacent à deux points fixes distincts $a,b$ est fixe : si $a\sim b$, $v$ est leur unique
voisin commun ($\lambda=1$) ; sinon $g$ permute les $\mu=2$ voisins communs de $a$ et $b$ et, étant d'ordre~3, les fixe. En
particulier, un sommet non fixe a au plus un voisin fixe.
\item \emph{$n_x\in\{2,8,14\}$.} Les voisins non fixes de $x\in F$ forment des orbites de taille~3, donc $n_x\equiv14\equiv2\pmod3$.
Et $n_x$ est pair : par $\lambda=1$, un voisin fixe $u$ de $x$ a un unique voisin commun avec $x$, qui est fixe par le point~1 ;
cela apparie les voisins fixes de $x$.
\item \emph{Comptage.} Par le point~1, il y a au plus $99-|F|$ arêtes entre $F$ et son complémentaire :
$\sum_{x\in F}(14-n_x)\le 99-|F|$, soit $15\,|F|\le 99+\sum_{x\in F}n_x$.
\item \emph{Conclusion.} Si $n_x=14$, tout sommet non adjacent à $x$ a deux voisins communs avec $x$, fixes, donc est fixe
(point~1) : $g=1$, exclu. Si $n_x=8$ et qu'aucun $n_y$ ne vaut $14$, soit $A$ l'ensemble des huit voisins fixes de $x$ et
$S=F\setminus(\{x\}\cup A)$, de cardinal $s$. Un $u\in A$ a pour voisins fixes $x$, au plus un sommet de $A$ ($\lambda=1$) et des
sommets de $S$ ; un $y\in S$ a au plus $\mu=2$ voisins dans $A$. Donc $\sum_{u\in A}n_u\le16+2s$ et
$\sum_{y\in F}n_y\le 8+(16+2s)+8s$. Comme $|F|=9+s$, le point~3 donne $15(9+s)\le 123+10s$, soit $12+5s\le0$ : impossible. Reste
le cas où tous les $n_y$ valent~$2$. Si $y\in F$ n'est ni $x$ ni un voisin de $x$, un voisin commun $a$ de $x$ et $y$ est fixe,
ainsi que le voisin commun $c$ de $x$ et $a$ (point~1) ; alors $a$ a trois voisins fixes $x,y,c$, contradiction. Donc $F$ est
contenu dans $x$ et ses deux voisins fixes : $|F|\le3$. \qedhere
\end{enumerate}
\end{proof}

"""
rep("%====================================================================\n\\section{Remarques}",
    new_sec + "%====================================================================\n\\section{Remarques}")

rep(r"""coordonnées fixes (point~1 du §4) la rend inutile. Pour le corollaire : en plus, Makhnev--Minakova.""",
    r"""coordonnées fixes (point~1 du §4) la rend inutile. Pour le corollaire : en plus, le comptage du lemme~\ref{lem:fix}
($\lambda=1$, $\mu=2$, $v=99$) ; aucune entrée extérieure.""")

rep(r"""\item \textbf{Vérification formelle.} Le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle} sont vérifiés en
Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans \texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement régulier
(\texttt{SimpleGraph.IsSRGWith}) : \texttt{C3.no\_free\_order3}, \texttt{C3.no\_triangle\_order3} (exactement trois points fixes ;
le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes). Ils ne dépendent que des axiomes
standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}, et n'emploient que des définitions de Mathlib : un
relecteur n'a à contrôler que ces énoncés. Les versions matricielles (théorème~\ref{thm:matrices} et §4) sont aussi vérifiées
(\texttt{C3.no\_pair}, \texttt{C3.Tri.no\_triangle\_pair}). Seul le théorème de Makhnev--Minakova (corollaire~\ref{cor:tout})
n'est pas formalisé. Sources : dossier \texttt{c3formal/}.""",
    r"""\item \textbf{Vérification formelle.} Tous les énoncés sont vérifiés en Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans
\texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement régulier (\texttt{SimpleGraph.IsSRGWith}).
L'énoncé final est \texttt{C3.no\_order3} : tout automorphisme $\sigma$ tel que $\sigma^3=1$ est l'identité (corollaire~\ref{cor:tout},
sans \cite{MM04}). Les étapes sont \texttt{C3.no\_free\_order3} (théorème~\ref{thm:libre}), \texttt{C3.no\_triangle\_order3}
(proposition~\ref{prop:triangle} ; le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes),
ainsi que les versions matricielles \texttt{C3.no\_pair} (théorème~\ref{thm:matrices}) et \texttt{C3.Tri.no\_triangle\_pair}
(§4). Tous ne dépendent que des axiomes standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}, et
n'emploient que des définitions de Mathlib : un relecteur n'a à contrôler que l'énoncé de \texttt{C3.no\_order3}. Sources :
dossier \texttt{c3formal/}.""")

rep(r"""l'étape~5 (réduction) et, au §4, le point~1.""",
    r"""l'étape~5 (réduction), au §4 le point~1, et le lemme~\ref{lem:fix}.""")

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
