# Un polynôme de la famille de Peter Giblin possède dix racines réelles distinctes

Le 2 septembre 2021, Peter Giblin a demandé si un polynôme de la forme

$$
P(x)=x^2+(x^2+1)(ax^8+bx^6+cx^5+dx^4+ex^3+fx^2+g)
$$

pouvait avoir dix racines réelles avec $a<0$ et $g>0$. Ses essais numériques suggéraient que ce maximum était inaccessible. [Question d’origine sur MathOverflow](https://mathoverflow.net/questions/403038/number-of-real-roots-of-a-degree-10-polynomial-with-several-parameters)

## Un exemple explicite

Prendre $S=\{2,4,9,11,-26\}$ et poser

$$
P(x)=-\frac{1}{34000}\prod_{s\in S}(x^2-sx-1).
$$

L’identité polynomiale suivante vérifie toutes les contraintes de la question en un seul calcul.

$$
34000P(x)=34000x^2+(x^2+1)
\bigl(-x^8+455x^6-5148x^5+17000x^4-5148x^3-34455x^2+1\bigr).
$$

En particulier, $a=-1/34000$, $g=1/34000$, et les coefficients de $x^7$ et de $x$ dans la parenthèse sont nuls.

## Pourquoi les dix racines sont distinctes

Pour chaque $s\in S$, le discriminant du facteur $x^2-sx-1$ vaut $s^2+4>0$. Ses racines sont

$$r_{s,\pm}=\frac{s\pm\sqrt{s^2+4}}{2}.$$

Une racine $r$ est non nulle, car le terme constant du facteur vaut $-1$. De l’équation $r^2-sr-1=0$, on tire $s=r-1/r$. Une même racine ne peut donc appartenir à deux facteurs différents. Les cinq facteurs fournissent exactement dix racines réelles distinctes.

## Comment construire l’exemple

Les facteurs $x^2-sx-1$ garantissent dès le départ deux racines réelles. Dans leur produit $Q$, choisir des paramètres $s$ de somme nulle annule les coefficients de $x^9$ et de $x$. Reste à obtenir la forme $P=x^2+(x^2+1)R$. Pour un polynôme réel, il suffit d’imposer $P(i)=-1$ pour que $x^2+1$ divise $P-x^2$. Or les cinq entiers choisis donnent exactement $Q(i)=34000$, d’où le facteur $-1/34000$.

[Énoncé en Lean](statements/mo-403038.lean) · [Preuve en Lean](proofs/mo-403038.lean)
