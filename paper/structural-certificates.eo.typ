#import "transported-control-figure.typ": transported-control-figure

#let title = "Prognoza profundo de unuflankaj regataj ĉelaj aŭtomatoj"
#let author = "Amamiya Miu"
#set document(title: title, author: author)
#set page(
  paper: "a4",
  margin: (x: 24mm, top: 22mm, bottom: 22mm),
  numbering: "1",
  number-align: center,
)
#set text(font: "Libertinus Serif", size: 11pt, lang: "eo")
#set par(justify: true, leading: 0.6em)
#set heading(numbering: "1.1")
#set math.equation(numbering: "(1)", supplement: [Ekvacio])
#show heading.where(level: 1): set block(above: 1.2em, below: 0.65em)
#show heading.where(level: 2): set block(above: 1em, below: 0.5em)
#show bibliography: set text(size: 10pt)

#let theorem(name, body) = figure(
  kind: "theorem",
  supplement: [Teoremo],
  numbering: "1",
  caption: [],
  block(width: 100%, above: 0.85em, below: 0.85em, breakable: false)[
    #set align(left)
    *Teoremo #context counter(figure.where(kind: "theorem")).display("1") (#name).*
    #emph(body)
  ],
)
#show figure.where(kind: "theorem"): it => it.body
#let qed = [#h(1fr) $square$]

#align(center, block(above: 0pt, below: 1.4em)[
  #text(size: 21pt, weight: "bold")[Prognoza profundo de unuflankaj
    #linebreak() regataj ĉelaj aŭtomatoj]
  #v(0.2em)
  #text(size: 13pt)[Klasifiko kontrolita per Lean]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*Resumo.* Ni klasifikas la prognozan profundon de unuflankaj ĉelaj aŭtomatoj,
kies fiksitaj regvortoj regas ĝisdatigon per restado kaj salto super
$bb(F)_2$. La eniro estas la eksplicita komenca fenestro kaj la eliro estas
la prognozita datuma bito ĉe la konuspinto. Plenumebla klasifikilo elektas
branĉon por ĉiu fiksa regulo. Unu logspac-unuforma familio de cirkvitoj de
De Morgan kun polinoma grando atingas la elektitan supran baron je ĉiu
tempo. La prognoza lingvo apartenas al logspac-unuforma $"NC"^0$ ĝuste kiam
la saltogardo estas ĉie nula, aŭ kiam ĝi estas ĉie unu kaj la restogardo
estas ĉie nula. Se la saltogardo estas nekonstanta, aŭ se ĝi estas ĉie unu
kaj la restogardo estas nekonstanta, la profundo estas $Theta(log(T+1))$.
Por la homogena Pascal-regulo ĉe $T>0$, la minimuma profundo en la
bazo de De Morgan estas $2p(T)+1$, kie $p(T)$ nombras la unubitojn de
$T$. La kontrolita unuforma generilo uzas profundon maksimume $3p(T)$. Por struktura komparo ni
solvas apartan unuvojan modelon kun transportata regado. Je pozitiva
tempo ĝia profundo estas unu ĉe egalaj rapidoj kaj precize
$ceil(log_2(T+1))$ ĉe malsamaj rapidoj. Lean 4 kontrolas la klasifikon,
la ligon inter dinamiko kaj finia prognozo, kaj la cirkvitajn barojn kaj
generilojn por la reguloj kun fiksita regado.

*Ŝlosilvortoj.* Ĉelaj aŭtomatoj, cirkvita profundo, logspaca unuformeco, Lean 4.
]

= Enkonduko

Kiuj kontroleblaj strukturaj kondiĉoj pri evoluregulo $F$ kaj observado
$O$ baras la cirkvitan profundon de $O(F^T(x))$ ĉe donitaj enirkodado
kaj cirkvita modelo? Algebra strukturo povas ebligi prognozon de ĉela
aŭtomato per cirkvitoj multe pli malprofundaj ol laŭtavola simulado @moore.
Ĉi tie ni demandas, kiuj fiksitaj gardoj en unuflanka dutraka aŭtomato
permesas konstantan profundon kaj kiel la profundo dependas de la observa tempo.

Nia ĉefa rezulto estas la kvarbranĉa klasifiko de reguloj kun fiksita
regado (@frozen-classification). Finia provo de la gardoj elektas branĉon.
Por ĉiu branĉo ni donas malsuprajn barojn je ĉiu tempo kaj unu efektivan
generilon, kies cirkvitoj atingas la koncernan supran baron je ĉiu tempo.
La homogena branĉo havas nemonotonan profundoprofilon, kiun regas la
unubitoj de la observa tempo. La deviga ordo de la saltoj permesas resumi ĉiujn vojojn al sama
finpunkto per du prefiksaj statistikoj. Duuma provo pri adicio sen reteno
montras kiuj koeficientoj restas post nuligo (@uniform-construction).
Kiel strukturan komparon ni ankaŭ solvas apartan unuvojan regulon kun
transportata regado (@transport-depth). Tie la relativa rapido determinas
kiom da malsamaj komencaj regbitoj la vojo renkontas.

= Antaŭpreparoj

Loka regulo sur konfiguracioj super $bb(Z)$ estas iteraciata $T$ fojojn.
La celo estas la datuma bito ĉe la origino. Ĉiu modelo en la ĉefaj rezultoj
havas unuflankan ĝisdatigon de radiuso unu, do ĝia komenca fenestro konsistas
el la ĉeloj $0, dots, T$. Por fiksita regado la eniro enhavas $q(T+1)$
regbitojn sekvatajn de $T+1$ datumaj bitoj. La regvorta larĝo $q$ kaj la du
gardaj cirkvitoj estas fiksaj sendepende de $T$. La valida vortlongo
$n=(q+1)(T+1)$ unike determinas $T$. La prognoza lingvo $L_(s,h)$ konsistas
el validaj vortoj kies prognozita bito estas unu. Ĝi malakceptas ĉiujn
aliajn longojn.

Niaj supraj baroj uzas buleajn pordegojn AND kaj OR de enira grado du, NOT
kaj konstantojn. Enira drato havas profundon nul, kaj NOT-pordego kostas
unu tavolon. Pordegoj povas reuzi elirojn kaj kunligi arbitrajn ĉelojn.
La malsupraj baroj de la klasifiko validas por arbitraj buleaj pordegoj
de enira grado maksimume du. Por fiksita regulo, $D(T)$ estas la minimuma profundo
de cirkvito de De Morgan sur valida fenestro je $T$. Skribu
$ell(m)=ceil(log_2 m)$ por $m >= 1$. Unuformaj cirkvitfamilioj estas
indeksitaj laŭ enirlongo. Determinisma logspaca transduktilo ricevas la
longon en unuma kodo kaj eligas la kompletan cirkvitkodon, inkluzive
de la pordegoj, drataro kaj eliro. Ĉiuj asertoj pri $"NC"$ uzas logspacan
unuformecon.

Koordinato estas _esenca_ se du valorasignoj, kiuj malsamas nur ĉe tiu
koordinato, donas malsamajn elirojn.

#block(breakable: false)[
*Baro el esencaj eniroj.* Cirkvito de profundo $d$ kaj enira grado
maksimume $b$ havas maksimume $b^d$ esencajn koordinatojn. Por $b >= 2$
funkcio kun $m >= 1$ esencaj koordinatoj do bezonas profundon almenaŭ
$ceil(log_b m)$.

_Pruvo._ Nur eniraj dratoj en la malantaŭa konuso de la eliro povas
influi ĝin. Je profundo nul la konuso havas maksimume unu eniron.
Je la sekva profundo ĉiu pordego havas maksimume $b$ antaŭulajn konusojn,
do indukto baras la nombron de eniraj dratoj per $b^d$. Se subcirkvitoj
estas reuzataj, ripeta nombrado de sama antaŭulo nur pliigas la baron. #qed
]

= Aŭtomatoj kun fiksita regado
== Formulo por la iteracio

Estu $a_i in {0,1}^q$ regvorto, $x_i in bb(F)_2$ komenca datuma bito,
kaj $s,h : {0,1}^q -> {0,1}$ la gardoj por restado kaj salto. La sinkrona
ĝisdatigo estas
$
  a'_i = a_i, quad
  x'_i = s(a_i) x_i + h(a_i) x_(i+1),
$ <frozen-rule>
kun datuma aritmetiko en $bb(F)_2$. Malantaŭa vojo finiĝanta ĉe ĉelo $k$
havas $k$ saltojn kaj $T-k$ restopaŝojn. Difinu
$
  e_k = product_(j=0)^(k-1) h(a_j), quad
  w_k = sum_(j=0)^k s(a_j),
$
kun la dua sumo en la naturaj nombroj. Por naturaj $w,r$, estu $M(w,r)$
la nombro de malfortaj komponaĵoj de $r$ en $w$ partojn. Por $w>0$, tiu
nombro estas $binom(w+r-1,r)$. $M(0,r)$ estas unu se $r=0$ kaj alie nul.

#theorem("Formulo por la iteracio")[
  Por ĉiu komenca agordo kaj tempo $T$, la datuma bito ĉe la origino estas
  $
    x_0(T) = sum_(k=0)^T e_k (M(w_k,T-k) mod 2) x_k.
  $ <frozen-sum>
  La sama idento validas ĉe ĉiu ĉelo post translacio de la indicoj.
]<frozen-iterate>

_Pruvo._ Disvolvi la lokan rikuron unufoje en ĉiu paŝo esprimas la eliron
kiel sumon laŭ malantaŭaj vojoj. Ĉiu salto devas esti permesita, kio
donas la faktoron $e_k$. Vojo vizitas la ĉelojn de $0$ ĝis $k$ laŭvice.
La atribuo de restopaŝoj al ĉiu permesanta ĉelo determinas la vojon,
inkluzive de restoj post la lasta salto. Estas $M(w_k,T-k)$ tiaj atribuoj.
Iliaj kontribuoj sumiĝas en $bb(F)_2$, donante @frozen-sum. La Lean-pruvo
establas la respondan rikuron por koeficientoj per indukto laŭ la iteracio
de @frozen-rule. La formulo uzas nur la komencan fenestron. #qed

== Profundoklasifiko

Estu $p(T)$ la nombro de unubitoj en la duuma prezento de $T$, kaj estu
$d_s,d_h$ la profundoj de la fiksitaj gardaj cirkvitoj. Garda funkcio
varias se ĝi alprenas ambaŭ buleajn valorojn. Ĉiuj subaj baroj estas
finiaj, ankaŭ ĉe $T=0$.

#figure(
  table(
    columns: (1.65fr, 0.75fr, 1.55fr),
    align: (left, left, left),
    inset: (x: 7pt, y: 5pt),
    stroke: none,
    table.hline(stroke: 0.7pt),
    table.header([*Garda kondiĉo*], [*Malsupra baro*], [*Unuforma supra baro*]),
    table.hline(stroke: 0.4pt),
    [$h equiv 0$], [$0$], [$1+d_s$],
    [$h equiv 1$, $s equiv 0$], [$0$], [$0$],
    [$h$ varias, aŭ $h equiv 1$ kaj $s$ varias],
      [$ell(T+1)$], [$O(log(T+2))$],
    [$s equiv h equiv 1$], [$p(T)$], [$3p(T)$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [Profundobaroj je validaj longoj por fiksitaj gardoj.],
  kind: table,
  supplement: [Tabelo],
) <regimes>

#theorem("Unuforma klasifiko")[
  Por ĉiu fiksa paro de gardaj cirkvitoj ekzistas unu logspac-unuforma
  familio de cirkvitoj de De Morgan kun polinoma grando, kiu decidas la
  tutan lingvon kaj atingas la koncernan supran baron en @regimes ĉe ĉiu
  valida longo. Ĝia profundo estas $O(log(n+2))$ ĉe ĉiuj longoj. La
  malsupra kolumno baras $D(T)$ de malsupre kaj validas eĉ por arbitraj
  buleaj pordegoj de enira grado maksimume du. La kondiĉo por konstanta
  profundo estas
  $
    L_(s,h) in "logspac-unuforma " "NC"^0
    quad <=> quad h equiv 0 or (h equiv 1 and s equiv 0).
  $
]<frozen-classification>

== Pruvo de la unuforma klasifiko

_Loka kazo kaj ŝovo._ Por $h equiv 0$ kaj $T>0$, idempotenteco donas
$s(a_0)x_0$. Pura ŝovo eligas $x_T$. Je $T=0$ ĉiu regulo eligas $x_0$.

_Variaj gardoj._ Kiam $h$ varias, nuligu ĉiujn datumajn bitojn krom $x_T$.
La restanta termo en @frozen-sum estas $x_T product_(j=0)^(T-1) h(a_j)$,
sendepende de $s$. Nekonstanta bulea gardo havas esencan biton, kiel montras
vojo de unubitŝanĝoj inter du vortoj kun malsamaj gardvaloroj. Ĉiu el la
unuaj $T$ regvortoj kontribuas unu esencan biton sub tiu limigo. Ankaŭ $x_T$
estas esenca. Se $h equiv 1$ kaj $s$ varias, fiksu $s(a_0)=1$ kaj $s(a_i)=0$
ĉe la ĉeloj $1$ ĝis $T$. Tiam $w_k=1$ por ĉiu $k$ kaj @frozen-sum estas
la pareco de ĉiuj $T+1$ datumaj bitoj. Ambaŭ kazoj donas la saman
malsupran baron per la esencaj koordinatoj.

La konstruo en @uniform-construction donas la supran baron en ĉi tiu branĉo.

_Homogena Pascal-regulo._ Por $s equiv h equiv 1$, la koeficientoj estas
$binom(T,k) mod 2$. Super $bb(F)_2$ la idento
$
  (1+z)^T = product_(j : "bit"_j(T)=1) (1+z^(2^j))
$
montras, ke aperas ĝuste la duumaj submaskoj de $T$. Iliaj $2^(p(T))$
datumaj bitoj estas esencaj. La logaritma malsupra baro do estas $p(T)$.
Ekvilibra XOR-arbo reduktas tiujn foliojn en $p(T)$ rondoj. Cirkvito de
De Morgan kun maksimume tri tavoloj realigas ĉiun XOR. La unuforma
generilo trairas $k=0, dots, T$, eligas la dratojn de la submaskoj kaj
seriigas regulan XOR-reduktilon kun $5 p(T) 2^(p(T))$ pordegoj.

_Unu sola unuforma familio._ La gardaj cirkvitoj kaj la elektita branĉo
estas fiksaj. La logspaca transduktilo eligas la prognozilon de tiu branĉo
ĉe validaj longoj kaj malakceptan cirkviton alie. Ĝia polinoma elirlongo
baras la nombron de pordegoj. La lokaj kaj ŝovaj branĉoj havas konstantan
baron. En la varia branĉo la malsupra baro kreskas laŭ $T$. En la homogena
branĉo ĝi kreskas laŭ la tempoj $T=2^r-1$. Tio pruvas la karakterizon de
konstanta profundo. #qed

La akompana klasifikilo kontrolas konstantecon de la gardoj per prefiksa
trairo de regvortoj. Lean pruvas, ke ĝia liverita valoro estas ekvivalenta
al la kondiĉo de la elektita branĉo. La konstantecoprovo haltas ĉe la unua
kontraŭekzemplo kaj en la plej malbona kazo povas viziti $2^q$ vortojn.

== Preciza profundo de la Pascal-regulo <pascal-exact>

Skribu $p=p(T)$ kaj $N=2^p$. La Pascal-eliro estas la pareco de $N$
eniroj. Se XOR estas unu du-enira pordego, ekvilibra arbo atingas la
malsupran baron $p$. En la bazo de De Morgan la minimuma profundo estas
nul ĉe $T=0$ kaj $2p+1$ ĉe $T>0$.

_Pruvo._ Por la supra baro, ĉe ĉiu folio pretigu la biton kaj ĝian
negacion. Interna nodo ricevas la du parecojn $a,b$ kaj iliajn negaciojn.
Ĝi kalkulas $(a and not b) or (not a and b)$ kaj
$(a and b) or (not a and not b)$ per du tavoloj. Unu tavolo de foliaj
negacioj kaj la $p$ internaj niveloj kune kostas $2p+1$ tavolojn.

Por la malsupra baro, fiksu la neesencajn enirojn al konstantoj kaj
malfaldu la cirkviton en formulon sen pliigi ĝian profundon. Puŝu la
negaciojn ĝis la folioj kaj simpligu la konstantojn. La pareca baro de
Khrapchenko postulas almenaŭ $N^2$ literalajn foliojn @khrapchenko.
Puŝi negaciojn ne ŝanĝas la folinombron, kaj simpligi konstantojn povas
nur malpliigi ĝin. Formulo de profundo maksimume $2p$ havas maksimume
$2^(2p)=N^2$ foliojn, kun egaleco nur por plena duuma arbo kies folioj
ĉiuj troviĝas ĉe profundo $2p$. Tia arbo havas nur AND- kaj OR-pordegojn
kaj do kalkulas monotonan funkcion. Pareco de $N>=2$ eniroj ne estas
monotona. La profundo devas do superi $2p$. #qed

La minimuma profundo en la bazo de De Morgan falas de $2r+1$ ĉe
$T=2^r-1$ al tri ĉe $T=2^r$ por $r>=2$. Lean kontrolas la optimumon je
ĉiu tempo en ambaŭ pordegaj bazoj. La unuforma klasifiko uzas la
apartan generilon kun profundo $3p$ en @regimes.

== Unuforma prognoza cirkvito <uniform-construction>

Estu $B(a)$ la aro de pozicioj de unubitoj en la duuma prezento de $a$.
Por $w>0$, laŭ la teoremo de Lucas, $M(w,r)$ estas nepara ĝuste kiam
$B(r) subset.eq B(w+r-1)$ @rowland. Ekvivalente, adicii $r$ kaj $w-1$
produktas neniun retenon. Efektive, se la sumo enhavas ĉiujn unubitojn
de $r$, subtrahi $r$ forviŝas tiujn bitojn sen prunto kaj lasas la bitojn
de $w-1$. Kun la kazo $w=0$ la provo fariĝas
$
  M(w,r) mod 2 = 1 quad <=> quad
  (w=0 and r=0) or (w>0 and B(r) inter B(w-1) = emptyset).
$ <no-carry>

La saltprefikso $e_k$ determinas ĉu vojo povas atingi $k$. Se la saltoj
estas eblaj, sufiĉas la nombro $w_k$ de ĉeloj permesantaj restadon,
ĉar ĉiu tia ĉelo povas akcepti arbitran nombron de restoj. Ekzemple,
se estas du tiaj ĉeloj kaj unu resto por distribui, la du eblaj vojoj
nuligas unu la alian. En @no-carry tio estas la komuna plej malalta
bito de $r=1$ kaj $w_k-1=1$.

*De la provo al cirkvito.* Taksu la gardojn paralele. Kalkulu ĉiun
$e_k$ per ekvilibra AND-arbo kaj ĉiun $w_k$ per nombrilo kun konservataj
retenoj. Ĉiu kunigrondo kunpremas du parojn de vortoj en unu je
konstanta profundo. La fina adicio propagas retenojn tra nur
$O(log(T+2))$ bitoj. Por ĉiu $k$ la generilo konas $r=T-k$. Ĝi kontrolas
@no-carry per duuma trairo por ĉiu kandidata nombro $j=0,dots,k+1$.
La cirkvito testas egalecon al $w_k$ por la kandidatoj kiuj trapasas.
Maksimume unu kandidato kongruas. Multipliku la elektitan biton per
$e_k x_k$ kaj prenu parecon tra la ĉeloj. La konstruo uzas konstantan
nombron de logaritmprofundaj stadioj kaj polinoman grandon eĉ kun
aparta nombrilo por ĉiu prefikso.

*La kontrolita generilo.* Lean kontrolas komunan malkodilon por ajna
tempo $u$ en la fenestro. La generilo konstruas la tabelon por ĉiuj
tiaj tempoj per la bitprovo de Lucas kaj elektas la vicojn por $T$ per
tempoetikedo kun unu sola unubito. La etikedo realigas la kunmetan
interfacon per vojigo de dratoj laŭ la duumaj ciferoj de $T$. Ĉiu
parecbanko legas la plej malaltan biton de nombrilo kun konservataj
retenoj. Logspaca transduktilo eligas la kompletajn listojn de
pordegoj kaj eliroj kaj rekalkulas la referencojn. La eksplicita
profundobaro estas $104(ell(T+3)+1)+max(d_s,d_h)$. @depth-budget priskribas
la aranĝon kaj la rimedokalkulon.

= Transportata regado kiel struktura komparo

En ĉi tiu aparta modelo la rega trako havas propran dinamikon kaj la
datumoj sekvas unu vojon. Fiksu la rapidojn $u,v in {0,1}$ kaj la buleajn
regan kaj datuman trakojn $(c_i,d_i)$. La sinkrona regulo estas
$
  c'_i=c_(i+u), quad d'_i=c_i and d_(i+v).
$ <transport-rule>
#block(breakable: false)[
La fenestro havas $2(T+1)$ bitojn. La sola malantaŭa datuma vojo donas
ĉe ĉelo $i$ kaj tempo $T$ la valoron
$
  d_(i+v T) and
  and.big_(k=0)^(T-1) c_(i+k v+(T-1-k)u),
$ <transport-iterate>
kun komencaj bitoj en la dekstra flanko kaj malplena konjunkcio je $T=0$.
]

#theorem("Preciza profundo ĉe transporto")[
  La profundo estas nula je $T=0$. Por $T>0$ ĝi estas precize unu se $u=v$
  kaj precize $ell(T+1)$ se $u != v$. La konstruo de la supra baro uzas
  kompletigitan AND-arbon kun maksimume $2m$ du-eniraj AND-pordegoj por
  $m$ esencaj eniroj. La malsupra baro validas por ĉiuj prognozaj buleaj
  cirkvitoj kun enira grado maksimume du.
]<transport-depth>

_Pruvo._ Ĉe la $k$-a paŝo de la malantaŭa vojo ni legas la regbiton ĉe
ĉelo $i+k v$ kaj tempo $T-1-k$. Ĝia komenca pozicio estas
$i+k v+(T-1-k)u$, kio pruvas @transport-iterate. Je $T=0$ la respondo
estas la enira drato $d_i$. Ĉe pozitiva tempo kun egalaj rapidoj
ĉiuj regindicoj koincidas, do restas konjunkcio de unu regbito kaj unu
datuma bito. Ĝenerale la komenca regindico estas $i+(T-1)u+k(v-u)$.
Kun malsamaj rapidoj, la komencaj regindicoj estas
$i, dots, i+T-1$ en antaŭa aŭ inversa ordo. Ĉiu malsama faktoro estas
esenca, ĉar ŝanĝi ĝin dum ĉiuj aliaj faktoroj estas unu ŝanĝas la eliron.
Estas du esencaj koordinatoj ĉe egalaj rapidoj kaj $T+1$ ĉe malsamaj
rapidoj. Por $m$ faktoroj, ekvilibra AND-arbo de alto $ell(m)$ atingas
la baron el esencaj eniroj. Kompletigo ĝis la sekva potenco de du uzas
$2^(ell(m))-1 <= 2m$ du-enirajn pordegojn. #qed

#transported-control-figure(
  caption: [Komenca regpozicio $j(k)$ ĉe la malantaŭa paŝo $k$ por $i=0$ kaj $T=4$.
    Ambaŭ vojoj finiĝas ĉe la komenca datuma bito $d_4$.],
  alt: "Maldekstre, ĉe egalaj rapidoj, ĉiuj kvar paŝoj legas la komencan regbiton 3. Dekstre, ĉe malsamaj rapidoj, ili sinsekve legas la komencajn regbitojn 0, 1, 2 kaj 3.",
  supplement: [Figuro],
) <transport-controls-figure>

En @transport-controls-figure la datuma vojo restas fiksa kaj nur $u$ varias.
La paro $(u,v)=(0,0)$ estas la fiksita kazo sen salto kun restogardo $c_i$.
Ŝanĝi nur $u$ al unu donas logaritman profundon, kvankam la datumoj neniam
saltas. Por $(u,v)=(1,1)$ ambaŭ trakoj moviĝas, sed ilia egala rapido donas
konstantan profundon. Por ĉi tiu unuvoja regulo gravas la nombro de
malsamaj komencaj regbitoj laŭ la datuma vojo en ĝia moviĝanta referenca
sistemo. La kadro por tempovariaj koeficientoj en @moore kovras ĉi tiun
regulon. Por finiaj buleaj monomiaj sistemoj, la rilato inter la variabloj
de iteracio kaj dependecaj promenoj de fiksa longo estas klasika
@boolean-monomial. En la finia prognoza fenestro la du ŝovoj eksplicite
determinas tiun variablaron.

= Evoluanta regado kun branĉado <branching-boundary>

*Unuforma transporto.* Permesu ambaŭ termojn en @frozen-rule kaj
transportu la tutan regtrakon per $a_i(t+1)=a_(i+1)(t)$. En la reflektita
moviĝanta koordinatsistemo $y_j(t)=x_(-j-t)(t)$ anstataŭigo donas
$
  y_j(t+1)=h(a_(-j-1)(0)) y_j(t)+s(a_(-j-1)(0)) y_(j+1)(t).
$
En tiu sistemo la regado estas fiksa kaj la gardoj interŝanĝas rolojn.
La observado $x_0(T)$ egalas al $y_(-T)(T)$, kies komenca datuma fenestro
estas la inversigo de la origina fenestro. La fiksa regfenestro enhavas
$a_(T-1)(0),dots,a_0(0)$ kaj unu kompletigan vorton. Neniu resto povas
okazi ĉe la lasta virtuala ĉelo, do la kompletiga vorto ne influas la
rezulton. La du prefiksaj statistikoj plu funkcias en tiu sistemo, kun
interŝanĝitaj roloj de restado kaj salto. Lean kontrolas la
koordinatŝanĝon kaj la cirkvitan redukton je ĉiu tempo, inkluzive de
la nova enira drataro.

*Adicia regdinamiko.* Nun unu regbito evoluas laŭ
$c_i(t+1)=c_i(t)+c_(i+1)(t)$ kaj la datumoj laŭ
$x_i(t+1)=c_i(t)x_i(t)+x_(i+1)(t)$. Ambaŭ ĝisdatigoj uzas $bb(F)_2$.
Ĉe $T=2$ la koeficiento de $x_1(0)$ ĉe la origino estas
$(c_0(0)+c_1(0))+c_1(0)=c_0(0)$. La komencaj paroj $(1,0)$ kaj $(0,1)$
havas la saman restonombron kaj saltan flagon por tiu finpunkto, sed
donas malsamajn koeficientojn. Resto ĉe la sama ĉelo nun povas legi
malsamajn gardvalorojn laŭ la tempo. Nombri la ĉelojn kiuj permesas
restadon ĉe tempo nul perdas la ordon necesan por determini nuligon.

Ankaŭ ĉi tiu regulo havas mallongan koeficientan priskribon. Estu
$Q_T(i)=c_i(T)+c_(i+T)(0)$ la Pascal-pareco de la komencaj regbitoj sen
ĝia plej dekstra termo. Por $0 <= k < T$, estu
$
  P_(T,k)(i)=product_(j=k+1)^(T-1)(1+c_(i+j)(0)).
$
Tiam la koeficiento de $x_(i+k)(0)$ en $x_i(T)$ estas $P_(T,k)(i) Q_T(i)$
por $k<T$, kaj unu por $k=T$. Unu sola pareco do estas komuna al la
finpunktoj, kaj testo pri nula sufikso elektas kiuj ricevas ĝin.

_Pruvo._ Nomu la koeficienton $b_(T,k)(i)$ kaj prenu ĝin nula ekster
la fenestro. La ĝisdatigo donas
$
  b_(T+1,k)(i)=c_i(T)b_(T,k)(i)+b_(T,k-1)(i+1).
$
Ĉar la kvadrato de bito egalas al ĝi mem,
$c_i(T)Q_T(i)=(1+c_(i+T)(0))c_i(T)$. Por $k<T$ la resta termo do havas
la sufiksan faktoron $P_(T+1,k)(i)$. Ankaŭ la salta termo havas ĝin,
ĉar $P_(T,k-1)(i+1)=P_(T+1,k)(i)$ por $k>0$. Por $k=0$ la salta termo
forestas, sed $Q_T(i+1)$ jam nuliĝas kiam $P_(T+1,0)(i)=1$: tiam la
sufikso nuligas ĉiun komencan regbiton en tiu pareco. Post elpreno de
la sufiksa faktoro, la sumo estas $c_i(T)+Q_T(i+1)=Q_(T+1)(i)$. Ĉe
$k=T$ la resta termo estas $c_i(T)$ kaj la salta termo estas
$Q_T(i+1)$, kun la sama sumo kaj malplena sufikso. Tio validas ankaŭ
ĉe $T=0$ ĉar $Q_0(i+1)=0$. La koeficiento de la nur-salta vojo ĉiam
estas unu. #qed

Resumo de bloko de sinsekvaj ĉeloj estas paro $(Z,V)$. La bito $Z$
indikas ĉu ĉiuj regbitoj en la bloko estas nulaj. La bito $V$ estas la
pareco de la datumaj bitoj kun nur nulaj regbitoj dekstre de ili en la
bloko. Unuopa ĉelo havas la resumon $(1+c_j(0),x_j(0))$. Kunigi du
blokojn kunmetas iliajn resumojn laŭ
$
  (Z_L,V_L),(Z_R,V_R) |-> (Z_L Z_R,V_L Z_R+V_R).
$
Ekvilibra arbo kalkulas $V$ por la unuaj $T$ ĉeloj, kun malplena
resumo $(1,0)$. La prognozo estas $x_T(0)+Q_T(0)V$. Dua arbo kalkulas
$Q_T(0)$ el la submaskaj dratoj. La du arboj uzas entute $O(T+1)$
pordegojn kaj havas profundon $O(log(T+2))$. La regulaj aranĝoj
estas sinsekve eligeblaj en logaritma spaco.

Ĉe pozitiva tempo la esencaj eniroj estas ĝuste la unuaj $T$ regbitoj
kaj ĉiuj $T+1$ datumaj bitoj. Fiksi ĉiujn datumajn bitojn krom $x_0(0)$
al nul donas $x_0(0)c_0(0) product_(j=1)^(T-1)(1+c_j(0))$, kio atestas
la esencecon de tiuj regbitoj. Fiksi $c_0(0)=1$ kaj
$c_1(0)=dots=c_(T-1)(0)=0$ donas la parecon de ĉiuj datumaj bitoj.
Sekvas la malsupra profundobaro $ell(2T+1)$. Lean kontrolas la koeficientan formulon por la efektiva kuplita
evoluo. La cirkvitaj baroj sekvas el la supra argumento.

= Rilata laboro

*Pascal-pareco kaj rapida prognozo.* La nombro $2^(p(T))$ de neparaj eroj
estas klasika. Rowland atribuas la duuman rezulton al Glaisher kaj derivas
ĝin el la teoremo de Lucas @rowland. Moore uzas Pascal-koeficientojn por
homogenaj adiciaj reguloj. Li ricevas logaritman profundon kun du-eniraj
pordegoj kaj logspac-unuforman $"ACC"^0$ kun nelimigitaj modulaj sumoj
@moore. Robison donas sinsekvan metodon por kalkuli unu koeficienton
el sola nenula komenca bito @robison. La optimumo je ĉiu tempo en
@pascal-exact sekvas el la klasika komplekseco de pareco. La kontrolita
unuforma familio realigas la Pascal-profilon ĝis konstanta faktoro.

*Dependaj linearaj trakoj kaj koeficienta formulo.* La Lemmo 1 de Moore
kunmetas spactempajn transigajn koeficientojn per dispartigo de la
tempintervalo. Teoremo 1 aplikas la algoritmon al kvazaŭ-rektaj produtoj.
Ekzemploj 1 kaj 3 kovras duumajn datumajn trakojn regatajn de alia
trako kaj triangulajn linearajn trakojn kiel en nia adicia modelo
@moore. Kun ekvilibraj XOR-arboj por la modulaj
sumoj, la ĝenerala metodo donas baron $O(log^2(T+2))$ por niaj duumaj
trakoj. Tempa senŝanĝeco kaj la unuflanka ĝisdatigo reduktas la fiksajn
koeficientojn al prefiksaj statistikoj. En alia kadro, Salo studas la
ĉellokan elekton inter identeco kaj XOR kun la dekstra najbaro sur
finia ringo @salo. Sekcio 3 uzas la lokajn mapojn de $s equiv 1$ kaj
$h(a)=a$ kaj traktas surĵetivecon kaj periodecon. Ĉi tie la regvortoj
estas parto de la eniro, kaj la eliro estas unu bito prognozita el
finia fenestro.

Paralelaj prefiksaj cirkvitoj estas klasikaj @ladner-fischer. Ĉi tie
ekvilibraj produtoj, nombrado per konservataj retenoj kaj koeficientaj
provoj donas la baron $O(log(T+2))$. La koeficiento en @frozen-sum havas
klasikan matrican analogon. La unupaŝa datuma mapo estas supra dudiagonala
operatoro sur la koncerna finia fenestro. La Teoremo 6.1 de Higham por
funkcio de tia matrico multiplikas la interajn eksterdiagonalajn
elementojn per dividita diferenco laŭ la diagonalaj elementoj @higham.
Por la monomo $z^T$, la dividita diferenco estas kompleta homogena
polinomo de grado $T-k$. Kun diagonalaj elementoj nul kaj unu ĝi
nombras la samajn malfortajn komponaĵojn. Oni povas specialigi la
polinoman identecon al entjeraj nul-unu-elementoj antaŭ redukto module
de du, sen dividado en $bb(F)_2$.

*Maŝina kontrolo kaj la signifo de fiksado.* Silváši kaj Tomášek formaligis
limigitajn kradojn kaj komputeblajn ĉelajn aŭtomatojn en Lean @silvasi.
La nuna formaligo kontrolas profundoklasifikon de regulfamilio kaj la
efektivan cirkvitgenerilon. La modelo de Ollinger kaj Theyssier kun
frostiĝo (*freezing*) postulas monotonan ordon por la tuta stato de ĉiu
ĉelo @ollinger. En @frozen-rule fiksa estas la regvorto, kaj la datumo
ĉe ĉelo povas cikli. La kontribuo ĉi tie estas la plenumebla kvarbranĉa
klasifiko, la kongruaj logaritmaj baroj por variaj gardoj kaj la pruvo
ke unu logspaca generilo por ĉiu regulo atingas la deklaritajn suprajn
barojn ĉe ĉiuj longoj. La antaŭaj komparoj lasas malferma la demandon
pri prioritato de tiu kombino.

= Formaligo kaj aplikkampo

La fenestra interfaco apartigas la senfinan dinamikon de finiaj
eniroj. `rawSample` legas la fenestron el konfiguracio, kaj
`decodeRaw` etendas arbitran validan fenestron al senfina konfiguracio.
Lean pruvas, ke specimenigo de la etendo redonas la liveritajn bitojn.
Ĝusteco sur specimenigitaj konfiguracioj do donas ĝustecon ĉe ĉiu valida
eniro. La transiro de tempa al longobaza indeksado elektas tiun saman
prognozilon ĉe validaj longoj kaj malakceptan cirkviton ĉe aliaj.

La pruvo de unuformeco generas la kodon de la cirkvito uzata por la
profundobaro, kun la varilongaj listoj de pordegoj kaj elirreferencoj.
La reuzeblaj kodkunmetiloj kontrolas referencobarojn kaj delokigon por
paralelaj bankoj kaj sinsekva kunmeto. Tio permesas al la generilo
rekalkuli unuopajn referencojn en logaritma spaco. La klasifika teoremo
uzas la elektitan cirkvitfamilion kiel unu atestanton pri ĝusteco,
grando, unuformeco kaj la baro je ĉiu tempo. La teoremo pri unuvoja transporto establas optimuman profundon por ĉiu
fenestrolongo aparte. Por branĉado kun unuforma transporto, Lean kontrolas
la koordinatŝanĝon kaj la cirkvitan redukton per nova enira drataro.

Ĉiu fiksita regvorto elektas unu el kvar lokaj datumaj mapoj
$0$, $x_i$, $x_(i+1)$ kaj $x_i+x_(i+1)$. Post fiksado de la regvortoj
la datuma dinamiko estas unuflanka kaj lineara. La eniro estas eksplicita
fenestro kun longo lineara laŭ $T$, kaj la cirkvito povas kunligi
arbitrajn ĉelojn.

La akompana Lean-projekto formaligas tri sufiĉajn kriteriojn. A konstruas
prognozilon el kunmetaj cirkvitoj kun limigitaj rimedoj. B transdonas
P-malfacilecon de la problemo pri cirkvitvaloro, se disponeblas atestilo
pri logspaca simulado. Ekskludo el unuforma $"NC"$ per B supozas
$"P" != "NC"$ kaj koncernas kompleksecklason. C donas senkondiĉan
malsupran profundobaron laŭ la nombro de esencaj eniroj, kiel en la
modeloj ĉi tie. Ĉe fiksitaj enira grado, dimensio, radiuso kaj bitlarĝo,
lumkonuso de polinoma volumeno limigas la *nombran baron* de C al
$O(log(T+2))$. La efektiva prognoza profundo povas superi tiun baron.
Lean kontrolas liveritajn atestilojn. Trovi ilin por arbitraj reguloj
estas aparta problemo. Por la familio kun fiksita regado, la plenumebla
klasifikilo elektas branĉon per konstantecaj provoj sur finia alfabeto.

= Konkludo

Ĉe fiksita regado, la konstanteco de la gardoj decidas la kazojn kun
konstanta profundo. Ĉe variaj gardoj prefiksaj statistikoj donas unuforman
prognozilon de logaritma profundo. La Pascal-profundon regas la unubitoj
de la observa tempo. Kun branĉado, unuforma transporto konservas la
fiksan resumon post koordinatŝanĝo. Adicia regdinamiko bezonas alian
resumon eĉ kiam ĉiuj saltoj estas eblaj. Tie la indukto fermiĝas ĉar
la koeficiento de la nur-salta vojo estas fiksa kaj la regado evoluas
per Pascal-konvolucio. Restas determini kiam simila koeficienta rekuro
fermiĝas se la evoluanta regado ankaŭ decidas la saltojn.

#heading(numbering: none)[Haveblo de la formaligo]

La fontoj en Lean kaj Typst kaj la kompilinstrukcioj troviĝas en la
#link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[projekta deponejo].
Uzu la deponejan revizion asociitan kun ĉi tiu PDF por trovi la deklarojn
en @lean-map.
La deponejo dokumentas la fiksitajn versiojn de Typst kaj la tiparojn
por rekonstrui la kvar eldonojn. Rulu #box[`./scripts/check.sh`] por la
strikta Lean-kompilo, transitiva aksiomkontrolo kaj negativa regresprovo.
La kontrolgvidilo distingas kompilajn rezultojn disde la revizio de modelaj
supozoj.
@lean-map listigas la deklarojn malantaŭ la ĉefaj rezultoj.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#heading(supplement: [Apendico])[Aranĝo de la generilo kaj kalkulo de la profundobaro] <depth-budget>

Estu $m=T+1$ kaj $B=ell(T+3)+1$. La registro konservas la tempoetikedon
$tau$, la restajn kaj saltajn flagojn kaj la datumojn en kvar blokoj
de larĝo $m$. La tempoindekso komenciĝas je nul. Legante la duumajn
ciferojn de $T$ de la plej signifa al la malplej signifa, ĉiu stadio
duobligas la indekson kaj aldonas unu se la cifero estas unu. La
operacioj vojigas dratojn kaj plenigas liberajn lokojn per nuloj.

Ĉe ĉelo $k$ la malkodilo enumeras la vicojn kun $0 <= u < m$ kaj
$0 <= j <= k+1$. Por vico kun $u>=k$ kaj nepara $M(j,u-k)$ ĝi eligas
la provon $(w_k=j) and tau_u$. Ĉiuj aliaj vicoj eligas nulon. Pareco
tra $j$ kaj poste tra $u$ elektas la koeficienton. La malkodilo
multiplikas ĝin per la saltprefikso kaj datumo, kaj prenas la parecon
tra $k$.

La normaligita nombrila arbo kostas maksimume $2+14b$ tavolojn,
inkluzive de pravalorizo kaj kopiado ĉe ĉiu kunigrondo, por vorta larĝo
$b=ell(a+1)$ de nombrilo pri $a$ bitoj. La fina adicio
kostas maksimume $1+8b$. Kune ili kostas maksimume $22(b+1)$. La nombriloj
do bezonas maksimume $22B$ tavolojn. Legi la plej malaltan biton por
pareco bezonas maksimume $23B$, inkluzive de la malplena kazo.
La profundopruvo asignas $5B$ al ĉiu vica testo por la bitkomparoj,
konjunkcio kaj tempoetikedo. La salta konjunkcio, barita per $5B$,
okazas paralele kun la elekto de koeficientoj. La buĝeto de la
malkodilo estas $22B+5B+3 dot 23B+2=96B+2 <= 98B$.
La pravalorizo de la registro kostas maksimume du tavolojn kun
normaligo. Sekvas maksimume $2 ell(T+1)$ registraj stadioj de
maksimume po du tavoloj, denove kun normaligo. Tio donas maksimume
$6B$ por la registra vojo kaj entute $104B+max(d_s,d_h)$ kun la gardoj.

La tabelo havas $m^2(m+3)/2$ vicojn. Estas $O(m^2)$ nombriloj kun
maksimume po $m+1$ eniraj bitoj. La regula aranĝo donas
$O(m^3 log^3(m+1))$ pordegojn por fiksitaj gardoj. Ĉiun pordegan
rikordon indeksas ĝiaj stadio, bloko, bitpozicio kaj loko en loka
ŝablono. Por paralelaj bankoj la serialigilo nombras pli fruajn
blokojn por kalkuli dratan deŝovon. En ĉeno de larĝo $W$, identecaj
pordegoj $y and y$ donas sinsekvajn indeksojn al la eliroj de stadio.
Post $G$ pordegoj kun $N$ ĉefaj eniroj, elirpozicio $a$ de tiu stadio
estas drato $N+G-W+a$. Tiel la serialigilo rekalkulas referencojn per
logaritmlarĝaj nombriloj kun fiksa nestada profundo kaj eligas la
listojn de pordegoj kaj eliroj laŭ la unume kodita longo.

#block(breakable: false)[
#set text(size: 9.5pt)
#heading(supplement: [Apendico])[Korespondo kun la Lean-deklaroj] <lean-map>

La vojoj sube estas relativaj al `PredictionDepth/`.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 3pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*Rezulto*], [*Lean-modulo kaj deklaro*]),
  table.hline(stroke: 0.4pt),
  [Iteracio kun fiksita regado],
  [`FrozenPascal/Semantics.lean` #linebreak() `iterate_data`],
  [Fenestra interfaco],
  [`FrozenPascal/GuardRules.lean` #linebreak() `rawSample_decodeRaw`],
  [Plenumebla klasifikilo],
  [`FrozenPascal/Classification.lean` #linebreak() `classify`, `classify_eq_iff`],
  [Unuforma klasifiko],
  [`FrozenPascal/UniformClassification.lean` #linebreak()
   `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [Unuforma prognozilo],
  [`FrozenPascal/UniformPrediction.lean` #linebreak()
   `uniformGuardedPrediction_code_logspace` #linebreak() `uniformGuardedPrediction_depth`],
  [Kodkunmeto],
  [`Complexity/CodeLogspace.lean` #linebreak() `compCode_logspace`],
  [Pascal-subteno kaj XOR-profundo],
  [`FrozenPascal/HomogeneousPascal.lean` #linebreak()
   `pascalSupport_card` #linebreak() `homogeneousNativeXorPrediction_depth`],
  [Preciza Pascal-profundo],
  [`FrozenPascal/PascalExactDepth.lean` #linebreak()
   `homogeneous_prediction_deMorgan_exact_depth`],
  [Transportata regado],
  [`TransportedControl.lean` #linebreak()
   `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
   `exact_prediction_depth`, `constant_depth_iff`],
  [Unuforma transporto kun branĉado],
  [`TransportedBranching.lean` #linebreak()
   `reverseFrame_iterate`, `prediction_correct` #linebreak()
   `prediction_depth`, `prediction_size`],
  [Koeficientoj por adicia regado], [`AdditiveBranching.lean` #linebreak()
    `trimmedParity_eq_sum`, `iterate_data`],
  table.hline(stroke: 0.7pt),
)
]

#bibliography("references.bib", style: "ieee", title: [Referencoj])
