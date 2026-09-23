# Resserre pdf/preuve_c3.tex pour tenir en 4 pages (2026-09-23).
import io
import os

p = os.path.join(os.path.dirname(__file__), '..', 'pdf', 'preuve_c3.tex')
s = io.open(p, encoding='utf-8').read()


def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80])
    s = s.replace(a, b)


rep(r"\setlength{\parskip}{3pt}", r"\setlength{\parskip}{2pt}")

rep(r"""La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur ; le théorème~1 et la
proposition~2 sont vérifiés en Lean~4, à partir de la définition d'un graphe fortement régulier.""",
    r"""La preuve est de l'algèbre linéaire élémentaire sur $\Z$ et $\Z[\omega]$, sans calcul par ordinateur.""")

rep(r"""\item \textbf{Contrôles numériques.} Le lemme « $d\equiv d'\pmod3$ » a été testé sans échec sur des graphes réels munis d'une action
libre d'ordre~3 : les graphes triangulaires $T(6)$, $T(7)$, $T(9)$, $T(10)$, $T(12)$, $T(13)$, $T(15)$, $T(18)$ et $T(21)$. Un cas réel donne $d\equiv d'\equiv2$ ($T(10)$). Il a
aussi été testé sur environ 1\,650 réseaux invariants aléatoires, avec un recalcul indépendant. Le test échoue bien lorsque le projecteur
n'est pas 3-entier, ce qui montre qu'il sait détecter une violation. La forme « $d=$ (premiers de $\theta-\theta'$) $\times$
(premiers de $\langle\one,\one\rangle$) » est observée exactement sur $T(15)$, $T(18)$ et $T(21)$.""",
    r"""\item \textbf{Contrôles numériques.} Le lemme « $d\equiv d'\pmod3$ » a été testé sans échec sur les graphes triangulaires
$T(n)$, $n\in\{6,7,9,10,12,13,15,18,21\}$, munis d'une action libre d'ordre~3 (un cas réel donne $d\equiv d'\equiv2$ : $T(10)$),
et sur environ 1\,650 réseaux invariants aléatoires, avec un recalcul indépendant ; le test échoue bien lorsque le projecteur
n'est pas 3-entier. La forme « $d=$ (premiers de $\theta-\theta'$) $\times$ (premiers de $\langle\one,\one\rangle$) » est
observée exactement sur $T(15)$, $T(18)$ et $T(21)$.""")

rep(r"""\item \textbf{Vérification formelle.} Le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle} ont été formalisés et
vérifiés en Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans \texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement
régulier (\texttt{SimpleGraph.IsSRGWith}) : \texttt{C3.no\_free\_order3}, \texttt{C3.no\_triangle\_order3} (exactement trois points
fixes ; le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes). Ils ne dépendent que des
axiomes standard \texttt{propext}, \texttt{Classical.choice} et \texttt{Quot.sound}. Le relecteur n'a à contrôler que ces énoncés,
qui n'emploient que des définitions de Mathlib. Seul le théorème de Makhnev--Minakova (corollaire~\ref{cor:tout}) n'est pas
formalisé.""",
    r"""\item \textbf{Vérification formelle.} Le théorème~\ref{thm:libre} et la proposition~\ref{prop:triangle} sont vérifiés en
Lean~4 (Mathlib \texttt{v4.35.0-rc2}), sans \texttt{sorry}, à partir de la définition de Mathlib d'un graphe fortement régulier
(\texttt{SimpleGraph.IsSRGWith}) : \texttt{C3.no\_free\_order3}, \texttt{C3.no\_triangle\_order3} (exactement trois points fixes ;
le triangle y est démontré) et \texttt{C3.no\_order3\_fix\_le3} (au plus trois points fixes), qui ne dépendent que des axiomes
standard de Lean. Un relecteur n'a à contrôler que ces énoncés. Seul \cite{MM04} (corollaire~\ref{cor:tout}) n'est pas formalisé.""")

io.open(p, 'w', encoding='utf-8', newline='\n').write(s)
print("ok")
