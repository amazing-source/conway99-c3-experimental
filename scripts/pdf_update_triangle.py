# Met à jour pdf/preuve_c3.tex : preuve du cas triangle sans Ishida, statut Lean (2026-09-23).
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80])
    s = s.replace(a, b)


rep(r"""\small Le théorème matriciel (théorème~5) est vérifié en Lean~4 / Mathlib (voir §5).}""",
    r"""\small Le théorème~1 et la proposition~2 sont vérifiés en Lean~4 / Mathlib (voir §5).}""")

rep(r"""et le second vaut $1$, car seul le premier $7$ y intervient. Le cas d'un triangle fixe se traite de la même façon.
Avec un théorème de Makhnev et Minakova, il en résulte que $\Gamma$ n'a aucun automorphisme d'ordre~3.
La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur.""",
    r"""et le second vaut $1$, car seul le premier $7$ y intervient. Le cas d'un triangle fixe se traite de la même façon, une fois
observé que les coordonnées des points fixes sont divisibles par~3.
Avec un théorème de Makhnev et Minakova, il en résulte que $\Gamma$ n'a aucun automorphisme d'ordre~3.
La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur ; le théorème~1 et la
proposition~2 sont vérifiés en Lean~4, à partir de la définition d'un graphe fortement régulier.""")

rep(r"""\begin{proposition}\label{prop:triangle}
$\Gamma$ n'a aucun automorphisme d'ordre~$3$ dont l'ensemble des points fixes est un triangle.
\end{proposition}""",
    r"""\begin{proposition}\label{prop:triangle}
$\Gamma$ n'a aucun automorphisme d'ordre~$3$ ayant exactement trois points fixes (ils formeraient un triangle).
\end{proposition}""")

rep(r"""D'après Makhnev et Minakova \cite{MM04}, les points fixes d'un automorphisme d'ordre~3 forment l'ensemble vide ou un triangle.
On conclut par le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle}.""",
    r"""D'après Makhnev et Minakova \cite{MM04}, les points fixes d'un automorphisme d'ordre~3 forment l'ensemble vide ou un triangle.
On conclut par le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle}. (Sans \cite{MM04} : le nombre de points fixes
est $\equiv 99\equiv0\pmod3$, donc ces deux énoncés excluent déjà tout automorphisme d'ordre~3 ayant au plus trois points fixes.)""")

old_start = r"""\section{Le cas d'un triangle fixe (proposition~\ref{prop:triangle})}"""
i = s.index(old_start)
j = s.index("%====================================================================\n\\section{Remarques}")
new_sec = r"""\section{Le cas de trois points fixes (proposition~\ref{prop:triangle})}

Soit $g$ d'ordre~3 ayant exactement trois points fixes $t_1,t_2,t_3$. Ils forment un triangle : si $t_i$ et $t_j$ n'étaient pas
adjacents, $g$ permuterait leurs $\mu=2$ voisins communs, donc les fixerait (il est d'ordre~3), et aurait au moins quatre points
fixes. Les $96$ autres sommets forment $32$ orbites libres, de sommets $(U,b)$, $U\le32$ ; on définit $A_b$, $Q$ et $M$
($32\times32$) comme au §2, et $\mathbf a[U,i]=A[(U,0),t_i]$. Alors $M$ est hermitienne, $M^2+M=12I$ (dans le calcul du §2, les
chemins passant par un $t_i$ et le terme en $J$ sont multipliés par $1+\omega+\omega^2=0$) et $Q\equiv M\pmod\pi$.

Les vecteurs de $\Z^{99}$ invariants par $g$ s'identifient à $\Z^{35}$ (une valeur par orbite libre, une par $t_i$). $A$ y agit par
\[
\tilde A=\begin{pmatrix}Q&\mathbf a\\3\mathbf a^{\mathsf T}&J_3-I_3\end{pmatrix},\qquad
\tilde A\one=14\one,\qquad \tilde A^2+\tilde A=12I+2\,\one w^{\mathsf T},
\]
où $w=(3,\dots,3,1,1,1)$ ($J$ agit par $\one w^{\mathsf T}$). Le produit scalaire de $\Z^{99}$ induit la forme $D=\mathrm{diag}(w)$,
pour laquelle $\tilde A$ est autoadjointe ($D\tilde A$ est symétrique). On pose $\Delta=\mathrm{diag}(I_{32},3I_3)$, de sorte que
$D\Delta=3I$.

\begin{enumerate}[leftmargin=*,nosep]
\item \emph{Les coordonnées fixes sont divisibles par~3.} Soit $\tilde N=11(\tilde A+4I)-2\,\one w^{\mathsf T}$. Comme à
l'étape~1, $(\tilde A-3I)\tilde N=0$ et $\tilde Nx=77x$ si $\tilde Ax=3x$ (alors $w^{\mathsf T}x=0$). Les trois dernières lignes
de $\tilde N$ sont nulles modulo~3 : $\tilde N[t_i,U]=33\,\mathbf a[U,i]-6$ et $\tilde N[t_i,t_j]=9+33\,\delta_{ij}$. Si
$x\in L=\ker_\Z(\tilde A-3I)$, on a donc $77\,x_{t_i}\equiv0$, soit $3\mid x_{t_i}$.
\item \emph{Gram pondéré.} Soit $B$ une base de $L$ (rang $r$) et $C$ telle que $CB=I$. Par le point~1, $\tilde G=\tfrac13
B^{\mathsf T}DB$ est une matrice entière, définie positive. La matrice $X=\tilde N\Delta$ est symétrique, $DX=3\tilde N^{\mathsf T}$,
et ses colonnes sont dans $L$. Comme à l'étape~3, $X=BKB^{\mathsf T}$ avec $K=CXC^{\mathsf T}$ entière, et
$3\tilde GK=B^{\mathsf T}DXC^{\mathsf T}=3(\tilde NB)^{\mathsf T}C^{\mathsf T}=3\cdot77\,I$. Donc $\tilde GK=77I$ et
$\det\tilde G=7^a11^b$.
\item \emph{Réduction modulo~3.} On a $X\equiv\mathrm{diag}\bigl(2(\bar Q+I),0\bigr)$ (les trois dernières colonnes sont
multipliées par~3, les trois dernières lignes sont nulles) et $\bar B=\binom{\bar B_1}{0}$ par le point~1. Réduites modulo~3, les
identités $X=BKB^{\mathsf T}$ et $K=CXC^{\mathsf T}$ ne font donc intervenir que le bloc $32\times32$ :
$2(\bar Q+I)=\bar B_1\bar K\bar B_1^{\mathsf T}$ et $\bar K=2\,\bar C_1(\bar Q+I)\bar C_1^{\mathsf T}$. Du côté de $M$, les
étapes~2 et~3 s'appliquent sans changement ($d'=7^c\equiv1$), et l'étape~5, mot pour mot, donne $r=r'$ et
$\det\tilde G\equiv d'\equiv1\pmod3$.
\item \emph{Le premier 11.} $W=\ker_\Z\bigl((\tilde A-3I)(\tilde A-14I)\bigr)$ contient $L$ et $\one$ et est de rang $r+1$ (sur
$\{w^{\mathsf T}x=0\}$, $\tilde A^2+\tilde A=12I$). La matrice $N_W=9(\tilde A+4I)-\one w^{\mathsf T}$ vaut $63$ fois le projecteur
sur $W\otimes\Q$ ; avec $X_W=N_W\Delta$, le calcul du point~2 donne $G_WK_W=189\,I$ pour $G_W=B_W^{\mathsf T}DB_W$, donc
$11\nmid\det G_W$. Comme $w^{\mathsf T}B=0$, la matrice de Gram (pour $D$) de $[B\,|\,\one]$ est
$\mathrm{diag}(3\tilde G,\,\one^{\mathsf T}D\one)=\mathrm{diag}(3\tilde G,99)$ ; comme à l'étape~4,
$3^r\cdot99\cdot\det\tilde G=\det(T)^2\det G_W$. Donc $b$ est impair et $\det\tilde G\equiv2\pmod3$, ce qui contredit le
point~3. \qed
\end{enumerate}

"""
s = s[:i] + new_sec + s[j:]

rep(r"""$0,1,2$ des coefficients de $Q$, ni aucun calcul. Pour la proposition~\ref{prop:triangle} : en plus, l'identité d'Ishida.
Pour le corollaire : en plus, Makhnev--Minakova.""",
    r"""$0,1,2$ des coefficients de $Q$, ni aucun calcul. Pour la proposition~\ref{prop:triangle} : de même (plus $\mu=2$ pour le
triangle). Une première version utilisait l'identité trace--rang d'Ishida pour obtenir $r=r'$ ; la divisibilité par~3 des
coordonnées fixes (point~1 du §4) la rend inutile. Pour le corollaire : en plus, Makhnev--Minakova.""")

rep(r"""\item \textbf{Vérification formelle.} Le théorème~\ref{thm:matrices} a été formalisé et vérifié en Lean~4
(Mathlib, version \texttt{v4.35.0-rc2}), sans \texttt{sorry} : le théorème \texttt{C3.no\_pair} ne dépend que des
axiomes standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}. Le relecteur n'a à contrôler que
les définitions (entiers d'Eisenstein, conjugaison, réduction $\rho$) et l'énoncé. Ne sont pas encore formalisés :
le lemme~\ref{lem:QM} (passage du graphe aux matrices) et la proposition~\ref{prop:triangle}.
\item \textbf{À relire en priorité.} L'étape~2 (facteur direct sur $\Z[\omega]$), l'étape~4 (valuation 11-adique) et
l'étape~5 (réduction). Pour la proposition~\ref{prop:triangle}, la normalisation par $D'$.""",
    r"""\item \textbf{Vérification formelle.} Le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle} ont été formalisés et
vérifiés en Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans \texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement
régulier (\texttt{SimpleGraph.IsSRGWith}) : \texttt{C3.no\_free\_order3}, \texttt{C3.no\_triangle\_order3} (exactement trois points
fixes ; le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes). Ils ne dépendent que des
axiomes standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}. Le relecteur n'a à contrôler que ces énoncés,
qui n'emploient que des définitions de Mathlib. Seul le théorème de Makhnev--Minakova (corollaire~\ref{cor:tout}) n'est pas
formalisé.
\item \textbf{À relire en priorité (preuve papier).} L'étape~2 (facteur direct sur $\Z[\omega]$), l'étape~4 (valuation 11-adique),
l'étape~5 (réduction) et, au §4, le point~1.""")

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
