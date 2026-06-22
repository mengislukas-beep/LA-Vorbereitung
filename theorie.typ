#import "../../style.typ": *

#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#show: setup


#stdtitle(
  [Theorie],
  [das sollte man können],
  [Lukas Mengis],
)
#pagebreak()
= The rank theorem

Let
$
  T : V -> W 
$
be a linear map, where V is finite dim.
Then
$
  dim(ker(T)) + dim(im(T)) = dim(V)
$
Proof.

Write $n := dim(V)$.\
Let $u_1,dots, u_k$ be a basis for $ker(T)$
$
  span(u_1,dots,u_k) = ker(T) 
$
Extend the basis of $ker(T)$ to a basis for $V$
$
  span(u_1,dots, u_k, v_1,dots, v_(n-k))
$
We can write the image of $T$ as followed
$
  im(T) = span(T(u_1), dots ,T(u_k), T(v_1),dots,T(v_(n-k))) = span(T(v_1),dots,T(v_(n-k)))
$
We claim that $T v_1,dots, T v_(n-k) $ form a basis for $im(T)$. This proofs that $T  v_1,dots, T v_(n-k) $ spans $im(T)$, so it remains to show that those vectors are linear indep.\
Let $a_1, dots, a_(n-k) in K $, and assume $sum_(i=1)^(n-k)a_i T v_i = 0$.\
Since $T$ is linear
$
  T(sum_(i=1)^(n-k)a_i v_i) = sum_(i=1)^(n-k)a_i T v_i = 0\
  => sum_(i=1)^(n-k)a_i v_i in ker(T)
$
Note $u_1, dots, u_k$ is a basis for $ker(T)$
$
  =>ex b_1, dots ,b_k quad st a_1 v_1 + dots, a_(n-k) v_(n-k) = b_1 u_1 + dots + b_k u_k. \
  => a_1 v_1 + dots, a_(n-k) v_(n-k) - b_1 u_1 - dots - b_k u_k = 0
$
But $u_1, dots, u_k, v_1,dots,v_(n-k)$ are linear independent (they form a basis)
$
  => a_1=dots=a_(n-k) = b_1 = dots = b_k = 0 
$
This proves that 
$
  T v_1, dots , T v_(n-k)
$
form a basis for $im(T)$\
Conclusion 
$
  dim(T) = n-k = dim(V) - dim(ker(T))\
  dim(ker(T)) +dim(im(T)) = dim(V)
$
#align(right)[$square$]
#pagebreak()

= Dual Maps
== Lemma(18.a.7)

The elemnts 
$
  v_1^star, dots, v_n^star
$
form a basis for $V^star$\
We denote this basis by
$
  B^star = (v_1^star, dots, v_n^star)
$
Moreover 
$
  fa l in V^star, quad l = um l(v_i) v_i^star.
$
Proof.\
Let $l in V^star$. We claim that
$
  l &= um l(v_i) v_i^star \
  <=> l(v) &= um l(v_i) v_i^star (v)
$ 
Indeed, $l$ and its representative sum are linear maps $V->K$, so it's enough to check that in the second equation holds for $v=v_1, v=v_2,dots ,v=v_n$, bc $v_1,dots,v_n$ form a basis for $V$. \
Set $v=v_k$
$
  um l(v_i) v_i^star (v_k) = um l(v_i) delta_(i k) = l(v_k).
$ 
The cleaim just proven shows that $v_1^star, dots, v_n^star$ span $V^star$\
since 
$
  dim(V^star) = dim(V) = n,
$
it follows that $v_1^star,dots, v_n^star$ form a basis for $V^star$.
#proved
== Lemma & def. (18.a.9)

Let $V,W$ be vect. spaces oves $K$. Let
$
  T : V-> W
$
be a linear map. Define a new map 
$
  T^star : W^star -> V^star, quad T^star (l) := l compose T quad fa l in W^star \

  (l : W -> K)
$
Then $T^star$ is a linear map. It is called the dual map to T.\
Proof.\
Let $l in W^star$, i.e. $l : W -> K$ linear.\
Clearly $l compose T : V -> K$ is a linear map (b.c. both $T$ and $l$ are), so $T(l) := l compose T in V^star$. This shows  $T^star : W^star -> V^star$ has its target indeed $V^star$ as claimed.\ \
We'll show now that $T^star$ is a linear map.\
Let 
$
  l in W^star, quad alpha in K
$
We have that 
$ 
  T^star (alpha l) in V^star\
  => T^star (alpha l )(v) &= ((alpha l) compose T) (v)\
  &= (alpha l) (T v)\
  &= alpha l (T(v))\
  &= alpha(l compose T)(v)\
  &= alpha(T^star l)(v)
$
$
  => T^star (alpha l) = alpha T^star (l)
$
Similarly one shows
$
  T^star (l_1+l_2) (v) &= ((l_1+l_2) compose T) (v)\
  &=  (l_1 compose T + l_2 compose T) (v)\
  &= (l_1 compose T) (v) + (l_2 compose T) (v)\
  &= T^star(l_1) (v) + T^star (l_2) (v)
$
$
  => T^star (l_1+l_2) =  T^star (l_1) + T^star (l_2)
$
#proved
== Lemma (18.a.11)
Let 
$
  S : V-> W
$
be a linear map between two f.dim. Vect.spaces $V$ & $W$ over $K$. Let $Beta$ be a basis for $V$ and $Kappa$ a basis for $w$.\
Cosider
$
  S^star : W^star -> V^star
$
and the bases $Kappa^star, Beta^star$ for $W^star,V^star$, respectibely. Then
$
  [S^star]_(Beta^star)^(Kappa^star) = [S^Beta_Kappa]^T
$
Proof.\
Write
$
  Beta = (v_1,dots,v_n) , quad Kappa = (w_1dots, w_m)\
A :=[S]^Beta_Kappa,quad A = (a_(i j)). 
$
$A$ satisfies 
$
  S v_j = um a_(i j) w_i
$
Now for $w`star in Kappa^star$ we have
$
  S^star w_j^star &= w_j compose S\
  &= um (w_j^star compose S)(v_i) v_i^star\
  &=um w_j^star (S(v_i)) v_i ^star\
  &= um w_j^star (sum_(k=1)^n a_(k i) w_k) v_i^star = um a_(j i) v_i ^star 
$
$=>$ coordinates of $S^star w_j^star$ in the basis $Beta^star = (v_1^star,dots,v_n^star)$ are
$
  vec(a_(j 1), dots.v,a_(j n))
$ 
row j in $A$, represented as col in the matrix $A^T$

#proved 
#pagebreak()
= The iso theoreme 18.c.5

Let $V,W$ be vect.sp.over $K$ and 
$
  T: v-> W
$
a linear map. Define a new map
$
  overline(T):  V slash_(ker(T)) -> im(T,)
$
Let $x in V slash_(ker(T)) $. Choose a represantative $v in V$ for x.
$
  x = [v]
$
Define
$
  overline(T) (x) := T(v)
$
Then 
+ $overline(T)$ well defined , and is linear map.
+ $overline(T) : V slash_(ker(t)) -> im(T)$ is an isomorphism.
+ The following diagram cummutes

#align(center)[
  #diagram(cell-size: 15mm, 
  $
    V edge(T,->) edge("d", pi, ->) &W\
    V slash ker(T) edge(overline(T), ->) &im(T) edge("u",->, i)
  $)
]
Proof.  
== $overline(T)$ is well defined.\

Suppose $x = [v] = [v']$, we need to show that $T(v) = T(v')$.\
Indeed $[v] =[v']$ implies that 
$
  v-v' &in ker(T).\
  &=> T(v-v')=0\
  &=> T(v) = T(v')
$
== $overline(T)$ is linear

$
  overline(T) (alpha[v]) &= overline(T)([alpha v])\
  &= T(alpha v) \
  &= alpha T(v) = alpha overline(T) ([v])
$
$
  overline(T)([v_1]+ [v_2]) &= overline(T)([v_1+v_2])\
  &= T(v_1 +v_2)\
  &= T(v_1) + T(v_2) = T([v_1]) + T([v_2])
$
== $overline(T)$ is injective
Let $x in ker(overline(T))$. Write $x$ as $x = [v]$ for some $v in V$ 
.\
Then
$
  overline(T)(x) = T(v) => v in ker(T) => x = [v] = 0_(v slash_(ker(T)))
$


== $overline(T)$ is surjective

Let 
$
  w in im(T). quad => ex v in V st T(v) = w\
  => overline([v]) = T(v) = w
$
This shows that 
$
  im(T) subset.eq im(overline(T)).
$
But by the def. of $ overline(T)$ we also have $im(overline(T)) subset.eq im(T)$
$
  => im(overline(T)) = im(T).
$
== The commutativity of the diagram

This follows immediately from the definitions. 