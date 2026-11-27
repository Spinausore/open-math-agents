# Un contre-exemple à l’inégalité de centralité de MathOverflow 200855

Dans sa [question du 24 mars 2015](https://mathoverflow.net/questions/200855), Liuchun Deng compare l’effet de deux modifications d’un graphe sur la centralité de ses sommets. Le graphe suivant, à douze sommets, donne une réponse négative.

## Construction

Prendre deux graphes complets à six sommets, l’un sur les sommets du haut numérotés de 0 à 5, l’autre sur les sommets du bas numérotés de 6 à 11. Relier chaque sommet du haut au sommet du bas de numéro supérieur de 6. Poser $a=0$, $b=1$, $c=6$ et $\lambda=1/14$. Les arêtes $ab$ et $ac$ existent, $bc$ est absente, et $0<1/14<1/11$.

Pour un graphe de matrice d’adjacence $H$, le score $v=(I-H/14)^{-1}\mathbf 1$ est l’unique solution du système

$$14v_i=14+\sum_{j\sim i}v_j.$$

En effet, la matrice $14I-H$ est strictement dominante sur la diagonale, chaque sommet ayant au plus onze voisins. Dans le graphe initial, tous les sommets ont six voisins. Le vecteur constant $y_i=7/4$ résout donc le système et vérifie les hypothèses $y_a\ge y_b$ et $y_a\ge y_c$.

## Les deux graphes modifiés

Après suppression de $ab$, les douze scores $x$ sont donnés dans leur ordre numérique par

$$x=\frac{1}{4848}(7840,7840,8365,8365,8365,8365,8428,8428,8463,8463,8463,8463).$$

Pour le vérifier à la main, écrire $u,v,w,s$ pour les quatre valeurs dans leur ordre d’apparition. Le système se réduit par symétrie à

$$
\begin{aligned}
14u&=14+4v+w, &14v&=14+2u+3v+s,\\
14w&=14+u+w+4s, &14s&=14+v+2w+3s .
\end{aligned}
$$

Après ajout de $bc$ au graphe **initial**, les scores $z$ des deux extrémités $b,c$ valent $p=1568/828$. Les scores de leurs partenaires respectifs dans l’autre clique valent $q=1470/828$, et les huit autres valent $r=1463/828$. Ces valeurs satisfont

$$
14p=14+p+2q+4r,\qquad 14q=14+2p+4r,\qquad 14r=14+p+q+4r .
$$

## Comparaison exacte

On obtient $x_a=490/303$, $y_a=y_c=7/4$ et $z_c=392/207$. L’inégalité proposée exige que le premier des deux rapports ci-dessous soit strictement supérieur au second. Or

$$
\frac{x_a}{y_a}=\frac{280}{303}
\quad<\quad
\frac{207}{224}=\frac{y_c}{z_c},
$$

puisque $280\times224=62720$ et $207\times303=62721$. L’écart exact est $1/67872$.

La [preuve Lean](proofs/mo-200855.lean) vérifie les 36 équations du contre-exemple, l’inversibilité et la négation de [l’énoncé formel](statements/mo-200855.lean).
