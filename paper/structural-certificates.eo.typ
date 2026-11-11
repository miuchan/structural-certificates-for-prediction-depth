#import "transported-control-figure.typ": transported-control-figure

#let title = "Strukturaj atestiloj pri prognoza profundo"
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
#show bibliography: it => {
  set text(size: 9.5pt)
  set par(leading: 0.42em, spacing: 0.45em)
  it
}

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
  #text(size: 21pt, weight: "bold")[Strukturaj atestiloj
    #linebreak() pri prognoza profundo]
  #v(0.2em)
  #text(size: 13pt)[Regataj ĉelaj aŭtomatoj kaj maldensaj korektoj]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*Resumo.* Ni studas du strukturojn, kiuj ebligas malprofundajn cirkvitojn
por prognozi ĉelajn aŭtomatojn el eksplicitaj komencaj fenestroj.
Por unuflanka fiksita regado, klasifikilo kontrolita per Lean elektas
inter konstantprofundaj, logaritmprofundaj kaj Pascal-kazoj.
Unu logspac-unuforma familio atingas la elektitan supran baron ĉe ĉiu
observotempo. En la Pascal-kazo la minimuma profundo en la bazo de
De Morgan estas $2p(T)+1$ por $T>0$, kie $p(T)$ nombras la unubitojn
de $T$. Transportata kaj adicia regado montras la efikon de ŝanĝoj
en la regulo sur la prognozilo. Por unuopa trajektorio, ni kontrolas
maldensan restaĵon rilate al fiksa lineara referenco per rekonstruo de
la plena konuso kaj kontrolo de ĉiu ĝisdatigo. Paralela nombrado donas
logspac-unuforman $"NC"^1$ kiam la restaĵa pezo estas konstanta aŭ la
nombro de permesitaj pozicioj estas logaritma. Tempa riparo uzas
polinoman grandon kun eksponento sendependa de la korektobuĝeto kaj
traktas ankaŭ limigitan nombron de nenulaj ĝisdatigaj tavoloj. Generilo
kun finia nombro de statoj liveras la malprofundan devigitan respondon
por ĉiu fiksa homogena duuma lineara referenco kun finia radiuso.

*Ŝlosilvortoj.* Ĉelaj aŭtomatoj, cirkvita profundo, logspaca unuformeco, Lean 4.
]

= Enkonduko

Kiuj kontroleblaj strukturaj kondiĉoj pri evoluregulo $F$ kaj observado
$O$ baras la cirkvitan profundon de $O(F^T(x))$ ĉe donitaj enirkodado
kaj cirkvita modelo? Algebra strukturo povas ebligi prognozon de ĉela
aŭtomato per cirkvitoj multe pli malprofundaj ol laŭtavola simulado @moore.
Ĉi tie ni demandas, kiuj fiksitaj gardoj en unuflanka dutraka aŭtomato
permesas konstantan profundon, kaj kiel rapide prognozi trajektorion kun
malmultaj diferencoj rilate al fiksa lineara regulo.

La unua rezulto estas la kvarbranĉa klasifiko de reguloj kun fiksita
regado (@frozen-classification). Finia provo de la gardoj elektas branĉon.
Por ĉiu branĉo ni donas malsuprajn barojn je ĉiu tempo kaj unu efektivan
generilon, kies cirkvitoj atingas la koncernan supran baron je ĉiu tempo.
La homogena branĉo havas nemonotonan profundoprofilon, kiun regas la
unubitoj de la observa tempo. La deviga ordo de la saltoj permesas resumi ĉiujn vojojn al sama
finpunkto per du prefiksaj statistikoj. Duuma provo pri adicio sen reteno
montras kiuj koeficientoj restas post nuligo (@uniform-construction).
Kiel strukturan komparon ni ankaŭ solvas apartan unuvojan regulon kun
transportata regado (@transport-depth). Tie la relativa rapido determinas
kiom da malsamaj komencaj regbitoj la vojo renkontas. La branĉaj
ekzemploj montras kiel transdoni prognozilon per koordinatŝanĝo kaj
kompili alian resumon kiam la fiksitaj statistikoj malsukcesas
(@branching-boundary).

La dua rezulto donas atestilon por unuopaj eniroj (@sparse-corrections).
La respondo al kandidata restaĵo rekonstruas la tutan dependokonusan
trajektorion. La lokaj ĝisdatigaj ekvacioj tiam determinas, ĉu la
kandidato estas la efektiva restaĵo. La sama kontrolo servas kaj paralelan
nombradon kaj tempan riparon, kun malsamaj grandaj kaj profundaj kostoj.

= Antaŭpreparoj

Loka regulo sur konfiguracioj super $bb(Z)$ estas iteraciata $T$ fojojn.
La celo estas la datuma bito ĉe la origino. La regataj modeloj havas unuflankan ĝisdatigon de radiuso unu, kun
komenca fenestro ĉe ĉeloj $0, dots, T$. En @sparse-corrections ni uzas
simetrian fenestron por ĝenerala finia radiuso. Por fiksita regado la eniro enhavas $q(T+1)$
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
koordinatŝanĝon kaj la redukton kun nulprofunda enira drataro kaj
identa eligo. Ĝia logspaca generilo transdonas la suprajn barojn
de la fiksita regulo al la transportata regulo.

*Adicia regdinamiko.* Nun unu regbito evoluas laŭ
$c_i(t+1)=c_i(t)+c_(i+1)(t)$ kaj la datumoj laŭ
$x_i(t+1)=c_i(t)x_i(t)+x_(i+1)(t)$. Ambaŭ ĝisdatigoj uzas $bb(F)_2$.
Ĉe $T=2$ la koeficiento de $x_1(0)$ ĉe la origino estas
$(c_0(0)+c_1(0))+c_1(0)=c_0(0)$. La komencaj paroj $(1,0)$ kaj $(0,1)$
havas la saman restonombron kaj saltan flagon por tiu finpunkto. Kun
datumoj $(0,1,0)$ ili donas malsamajn prognozojn. Tial neniu ellegilo de
tiu resumo kun la datuma kunteksto povas ĝuste prognozi ĉiun fenestron.
Lean kontrolas la kolizion sur la efektiva iteracio. Resto ĉe la sama
ĉelo nun povas legi malsamajn gardvalorojn laŭ la tempo, do gravas
la ordo de la regbitoj.

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

*La kontrolita prognozilo.* Por la unuaj $T$ ĉeloj la generita
cirkvito reduktas tribitajn resumojn $(Z,V,Q)$. $Z$ indikas ĉu ĉiuj
regbitoj de la bloko estas nulaj. $V$ estas la pareco de la datumaj
bitoj kun nur nulaj regbitoj dekstre en la bloko. $Q$ kolektas la
maskitan regan parecon. Estu $lambda_(T,j)=binom(T,j) mod 2$.
Ĉelo $j$ kontribuas $(1+c_j(0),x_j(0),lambda_(T,j)c_j(0))$.
Kunigo de apudaj blokoj donas la asocian operacion
$
  (Z_L,V_L,Q_L),(Z_R,V_R,Q_R) |-> (Z_L Z_R,V_L Z_R+V_R,Q_L+Q_R).
$
La idento estas $(1,0,0)$ kaj la ellego estas $x_T(0)+Q V$. La eniro
interplektas $T$ parojn de rega kaj datuma bito, poste donas $x_T(0)$.
La logspaca generilo kalkulas $T$ el la nepara enirlongo kaj uzas
la submaskan teston de Lucas por fiksi la maskojn. Ĝi malakceptas parajn
longojn. La kompililo de ordigitaj resumoj kompletigas per identoj kaj
duonigas la aktivan larĝon ĉe ĉiu nivelo. Lean kontrolas la generitan
familion, inkluzive de kopiaj pordegoj, kaj pruvas la pordegobaron
$108(T+1)$ kaj, por $T>=1$, la profundobaron $6+5ell(T)$.

*Malsupra baro.* Por $T>0$, fiksu $c_0(0)=1$ kaj nuligu ĉiujn aliajn
enirajn regbitojn. Ĉiuj datumaj koeficientoj fariĝas unu. La $T+1$
datumaj bitoj do estas esencaj. Lean kontrolas la malsupran baron
$ell(T+1)$ por ĉiuj buleaj cirkvitoj kun enira grado maksimume du.
La minimuma De Morgan-profundo do estas $Theta(log(T+1))$ kiam $T$
kreskas. Ĉe tempo nul la prognozo estas datuma projekcio. La formulo
donas ankaŭ pli akran nombradon surpapere. Se $x_0(0)=1$ estas la
sola nenula datumbito, la eligo estas
$c_0(0) product_(j=1)^(T-1)(1+c_j(0))$. Ĉiuj $T$ regbitoj do ankaŭ estas
esencaj, kio donas la nombran baron $ell(2T+1)$.


= Maldensaj korektoj laŭ trajektorio <sparse-corrections>

La antaŭaj strukturoj estas komunaj al ĉiuj eniroj de fiksa regulo.
Ĉi tiu atestilo koncernas unu trajektorion kaj unu observotempon. Ĝi
nombras diferencojn inter la efektivaj ĝisdatigoj kaj tiuj de fiksa
lineara referenco, ambaŭ taksataj ĉe la efektiva stato je ĉiu tempo.

== Komuna konuso kaj devigita respondo

Fiksu determinisman regulon $F$, homogenan linearan regulon $L$, nombron
$q>=1$ de trakoj kaj komunan radiusan baron $R>=1$. Por observotempo $T$,
la bitkoordinatoj je statotempo $t$ estas
$B_t=[-R(T-t),R(T-t)]_bb(Z) times {0,dots,q-1}$.
La najbareco de ĉiu ĉelo en $B_(t+1)$ troviĝas en la spaca fenestro de
$B_t$. Tial la limigoj $F_t,L_t:bb(F)_2^(B_t)->bb(F)_2^(B_(t+1))$
estas bone difinitaj. Indukto montras, ke finia iteracio kongruas kun
ĉiu senfina etendo de la komenca vorto $u$. Ni observas fiksan trakon
$a_*$ ĉe la origino je tempo $T$ kaj skribas $g_(T)(u)$ por tiu bito.
La valida longo $n=q(2R T+1)$ determinas $T$. Estas $V=q(T+1)(R T+1)=O(n^2)$
statbitoj kaj $M=V-n$ ĝisdatigaj elirbitoj. Okazaĵo $(t,i,a)$ estas
la bito $(i,a)$ en $B_(t+1)$, kiun kreas la ĝisdatigo de $t$ al $t+1$.

Estu $x_0=u$ kaj $x_(t+1)=F_(t)(x_t)$. La efektiva restaĵo kaj la devigita
respondo estas
$
  e_t^star = x_(t+1)+L_t x_t, quad
  y_0=u, quad y_(t+1)=L_t y_t+e_t .
$ <forced-recurrence>
La aritmetiko estas en $bb(F)_2$. La rektangula propagilo
$P_(s,t)=L_(t-1) dots L_s$ portas tavolon $s$ al tavolo $t$, kun la
identeca mapo ĉe $s=t$. Lineareco kaj indukto en @forced-recurrence donas
$
  y_t=P_(0,t)u+sum_(s=0)^(t-1)P_(s+1,t)e_s .
$ <forced-sum>
Skribu $S$ kaj $D$ por la grando kaj profundo de cirkvito, kiu eligas
*ĉiun* biton de la respondo. Ni kontrolas, ĉu $y_(t+1)$ egalas al
$F_(t)(y_t)$ ĉe ĉiu koordinato, inkluzive de tiuj kun nula kandidata
restaĵo. Lokaj kontroloj kaj ekvilibra konjunkcio uzas $O(V)$ pordegojn
kaj profundon $O(log(V+1))$. Skribu $v(u,e)$ por la rezulto. Se $e=e^star$,
la rekuro donas $y=x$ kaj la kontrolo sukcesas. Se la kontrolo sukcesas,
la respondo kaj la efektiva trajektorio havas la saman komencan staton
kaj kontentigas la saman ĝisdatigon ĉe ĉiuj koordinatoj. Indukto donas
$y=x$ kaj la rekuro tiam donas $e=e^star$. Sekve
$
  v(u,e)=1 <=> e=e^star .
$ <sparse-verifier>

== Paralela nombrado kaj tempa riparo

#theorem("Atestilo per nombrado")[
  Por listo de $N>=1$ kandidataj restaĵoj sendependa de la eniro,
  cirkvito eligas $(A,A and g_(T)(u))$, kie $A$ testas ĉu $e^star$ troviĝas
  en la listo. La grando estas $O(N(S+V+1))$ kaj la profundo estas
  $D+O(log(V+1)+log(N+1))$.
]<sparse-enumeration>

_Pruvo._ Kopiu la respondcirkviton por ĉiu kandidato kaj anstataŭigu
la restaĵajn enirojn per konstantoj. Prenu la disjunkcion de ĉiuj
kontroloj por $A$. Por la dua eliro prenu la disjunkcion de la
konjunkcioj de ĉiu kontrolo kun ĝia kandidata observado.
@sparse-verifier determinas la sukcesajn kandidatojn kaj ilian komunan
observitan valoron. La kopioj funkcias paralele. La du ekvilibraj
disjunkciarboj aldonas profundon $O(log(N+1))$. #qed

Restaĵon kun pezo maksimume $k$ reprezentas maksimume $k$ okazaĵadresoj.
Ordigu la adresojn kaj kompletigu la vicon ĝis longo $k$ per malplena
simbolo. La preciza nombro de kandidatoj estas
$sum_(j=0)^(min(k,M)) binom(M,j) <= (M+1)^k$. La generilo povas
trairi ĉiujn tiajn vicojn kaj interpreti ĉiun kiel aron, kun eventualaj
ripetoj. Por fiksa $k$, la nombriloj okupas $O(log(n+1))$ spacon. Se la
permesitaj pozicioj formas fiksan aron $J_T$ de grando $K$ kun grando kaj
indeksitaj adresoj kalkuleblaj en logspaco, ni trairas la $2^K$ asignojn sur $J_T$
kaj metas nulojn aliloke. La asigna nombrilo okupas logspacon kiam
$K=O(log(n+1))$. En ambaŭ okazoj la generilo ordigas laŭ tempo, ĉelo kaj
trako. Ĝi skanas la kodon de la respondo, metas la kandidatajn konstantojn
ĉe restaĵaj eniroj, delokas internajn dratnumerojn kaj eligas la lokajn
kontrolojn kaj ekvilibrajn reduktojn en indeksitaj blokoj. Polinoma
grando certigas logaritman larĝon de ĉiuj delokigoj kaj dratnumeroj.
Ĉe nevalida longo ambaŭ eliroj estas nulaj. Tial logspac-unuforma respondo
kun polinoma grando kaj logaritma profundo donas logspac-unuformajn
predikatojn en $"NC"^1$ pri aplikeblo kaj kondiĉa prognozo en ambaŭ okazoj.

#theorem("Atestilo per tempa riparo")[
  Ordigante la ĝisdatigajn elirbitojn laŭ tempo, dispartigu ilin
  en unuopajn bitojn aŭ en tutajn ĝisdatigajn tavolojn. Por buĝeto $k$,
  cirkvito eligas $(A,A and g_(T)(u))$, kie $A$ testas ĉu maksimume $k$
  blokoj enhavas nenulan efektivan restaĵon. La grando estas
  $O((k+1)(S+V+1))$ kaj la profundo estas $O((k+1)(D+log(V+1)))$.
]<sparse-repair>

_Pruvo._ Komencu kun $e=0$. En ĉiu raŭndo kalkulu la respondon $y$ kaj
la malkongruon $m_t=F_(t)(y_t)+y_(t+1)$. Trovu la unuan blokon kun
nenula malkongruo kaj aldonu tiun malkongruon al $e$ per XOR nur sur
tiu bloko. Se ĉio kongruas, konservu $e$.

Komence de ĉiu raŭndo, la nuna restaĵo egalas al $e^star$ en la prefikso
ĝis la laste riparita bloko kaj estas nula poste. Komence la prefikso
estas malplena. Ĉiuj ĝisdatigaj tavoloj antaŭ la unua ankoraŭ neriparita
nenula bloko jam havas la efektivajn restaĵojn, do la antaŭa stato de
tiu bloko estas ĝusta. Je ĝia ĝisdatiga tempo, $F_(t)(y_t)=x_(t+1)$ kaj
$y_(t+1)=L_t x_t+e_t$, do la malkongruo egalas al $e_t^star+e_t$.
Antaŭaj blokoj en la sama tavolo ankaŭ kongruas. Tial la raŭndo riparas
ĝuste la unuan mankantan nenulan blokon kaj konservas la aliajn. Se
neniu mankas, la plena kontrolo jam sukcesas. Post $k$ raŭndoj apliku
denove @sparse-verifier kaj konjunkciu ĝian rezulton kun la fina observado.

Kalkulu paralele ĉiujn malkongruajn bitojn kaj la flagon de ĉiu bloko.
Metu la flagojn ĉe la folioj de ekvilibra duuma arbo kaj kalkulu la
disjunkcion de ĉiu subarbo en suprena paso. Poste propagu prefiksojn
malsupren, kun nulo ĉe la radiko. La maldekstra ido heredas la prefikson
de sia patro, kaj la dekstra ricevas la disjunkcion de tiu prefikso kun
la flago de la maldekstra subarbo. Ĉe ĉiu folio la prefikso estas la
disjunkcio de ĉiuj antaŭaj flagoj. Elektu blokon kiam ĝia flago estas
unu kaj ĝia prefikso nulo. La du pasoj uzas $O(V)$ pordegojn kaj
profundon $O(log(V+1))$. Ĝisdatigi la restaĵajn bitojn aldonas konstantan
profundon. La $k$ riparoj kaj la fina respondo kun kontrolo donas la
asertitajn barojn. #qed

La aranĝo estas logspac-unuforma se la respondo estas unuforma kaj la
raŭnda buĝeto estas kalkulebla en logspaco kun polinoma supra baro.
La generilo trairas la stadiojn kaj blokojn, reuzas la respondkodilon
kun delokitaj eniroj, kaj konektas la riparitajn bitojn al la sekva
stadio. La drataron de la arbo donas la tavolaj kaj nodaj numeroj.
La eksponento dependa de $k$ en la nombrado cedas al la faktoro $k+1$.
Logaritmprofunda respondo donas unuforman $"NC"^1$ por konstanta $k$ kaj
unuforman $"NC"^2$ por $k=O(log(n+1))$. Tut-tavolaj blokoj permesas
arbitran nombron de nenulaj bitoj en ĉiu kalkulita tavolo. Unubitajn
blokojn regas la suma pezo de la restaĵo. Kiam $T=0$, ne estas okazaĵoj,
la malplena kontrolo sukcesas kaj la observado estas komenca bito.

== Unuforma respondo por ĉiu fiksa homogena lineara regulo

#theorem("Homogena lineara respondo")[
  Ĉiu fiksa homogena lineara regulo kun $q$ trakoj kaj radiuso $R$
  super $bb(F)_2$ havas logspac-unuforman plenan devigitan respondon
  sur la komuna konuso kun $O(V^2)$ pordegoj kaj profundo $O(log(V+1))$.
]<sparse-homogeneous-response>

_Pruvo._ Skribu $(L x)_i=sum_(delta=-R)^R A_delta x_(i+delta)$ kun
fiksaj matricoj kaj metu $H(X)=sum_(delta=-R)^R A_delta X^(delta+R)$.
La koeficiento de ĉelo $j$ al ĉelo $i$ post $r$ paŝoj estas la koncerna
matrica elemento de $[X^(j-i+R r)]H(X)^r$, aŭ nulo por eksponento ekster
la intervalo. Pro la fermiteco de la konuso tiuj estas la samaj
koeficientoj kiel en la finiaj propagiloj. Ili aperas en la racionala
matrica serio
$
  sum_(r>=0) Y^r H(X)^r = (I-Y H(X))^(-1).
$
Ĉiu elemento havas polinoman numeratoron $U$ kaj komunan denominatoron
$Q=det(I-Y H(X))$, kun $Q(0,0)=1$.

Por $a,b in {0,1}$, la operatoro $Lambda_(a,b)$ portas la koeficientojn
ĉe indeksoj $(2i+a,2j+b)$ al $(i,j)$. Tiu duuma sekcifunkcio aperas en
aŭtomataj algoritmoj por koeficientoj @abc-cartier.
Super $bb(F)_2$ ni havas $Q(X,Y)^2=Q(X^2,Y^2)$. La inverso de
$Q(X^2,Y^2)$ havas nur parajn eksponentojn en ambaŭ variabloj, do
la sekcifunkcio transigas ĝin kun duonigitaj eksponentoj. Apliko
al $(U Q)/Q(X^2,Y^2)$ donas
$
  Lambda_(a,b)(U/Q)=Lambda_(a,b)(U Q)/Q .
$
Por ĉiu variablo prenu la pli grandan el la gradoj de la komencaj
numeratoroj kaj $Q$. Multipliko per $Q$ kaj duonigo de la eksponentoj
konservas tiujn du barojn. Estas finie multaj eblaj numeratoroj super
$bb(F)_2$. Por trovi koeficienton, komencu kun la koncerna numeratoro kaj
legu la du duumajn indeksojn ekde la plej malaltaj bitoj, kompletigante
la pli mallongan per nuloj. Ĉe ĉiu bitparo anstataŭigu la numeratoron
per $Lambda_(a,b)(U Q)$. Fine liveru ĝian konstantan koeficienton,
ĉar $Q(0,0)=1$. La fiksaj transiroj kaj logaritmlarĝaj indeksaj nombriloj
donas logspacan koeficientgenerilon.

Por ĉiu elirbito, trairu la komencajn kaj pli fruajn devigajn bitojn en
@forced-sum. La generita koeficiento elektas, ĉu konekti la fontbiton
aŭ nulon al folio de ekvilibra XOR-arbo. Estas maksimume $V$ folioj en
ĉiu arbo kaj $V$ eliroj. XOR havas fiksgrandan realigon per pordegoj
de De Morgan. La nombriloj de tempo, ĉelo kaj trako donas la adresojn.
Kompletigo de la arboj ĝis komuna potenco de du ebligas kalkuli dratajn
delokigojn per logaritmlarĝa entjera aritmetiko. Tiel la generilo eligas
la tutan respondcirkviton en logspaco. #qed

Tiu teoremo liveras la respondan cirkviton bezonatan de ambaŭ atestiloj
por homogenaj linearaj fonoj sur la krado. Ĉe lineara fono, kiu dependas
de tempo aŭ pozicio, @forced-sum plu validas, kaj malprofunda unuforma
respondo estas aparte liverenda.

== Aplikoj kaj limo <sparse-examples>

La unutraka Pascal-referenco $(L x)_i=x_i+x_(i+1)$ post $r$ paŝoj uzas
ĝuste la delokigojn, kies unubitoj aperas en $r$. Tio estas la duuma
koeficienttesto en @pascal-exact. La efektiva OR-regulo
$(F x)_i=x_i or x_(i+1)$ havas restaĵon $x_i x_(i+1)$ ĉe ĉiu ĝisdatigo.
La aparte konata observado ĉe la pinto estas $or.big_(j=0)^T x_j$,
per kiu oni povas kontroli la prognozon ĉe akceptitaj eniroj.

*Densaj restaĵoj kun malprofunda prognozo.* El komenca fenestro de
nur unubitoj, ĉiuj statbitoj en la konuso restas unu. Ĉiu Pascal-ĝisdatigo
donas nulon, do ĉiuj $M=T^2$ restaĵbitoj estas unu. Por ĉiu eniro la
rekta OR-formulo tamen donas ekvilibran duuman arbon de profundo $ell(T+1)$.
Komparu la nulvorton kun vorto havanta nur unu biton de la disjunkcio je
unu. Tio montras, ke ĉiu el la $T+1$ koncernaj bitoj estas esenca. La
esenc-enira baro donas la saman malsupran baron por ĉiuj cirkvitoj kun
enira grado maksimume du.

Por reigebla nelineara ekzemplo, uzu tri trakojn $(a,b,c)$ kaj apliku
la lokan ciklon $110 -> 101 -> 011 -> 110$, konservante ĉiujn aliajn
statojn. Poste transportu $a$ dekstren, $b$ maldekstren kaj lasu $c$
senmova. Kaj la permuto kaj la transporto estas inversigeblaj kaj
konservas la nombron de unubitoj en konfiguracioj kun finia subteno.
La ciklo fiksas la tri bazajn vektorojn kaj ŝanĝas $110$, do la regulo
estas nelineara. Kun libera transporto kiel $L$, ĉiu devigita eliro
estas la XOR de la komenca bito kaj ĉiuj impulsoj laŭ ĝia karakteriza
linio. Ekzemple,
$
  a_(i)(t)=a_(i-t)(0)+sum_(s=0)^(t-1)e^a_(s,i-(t-1-s)).
$
La karakteriza linio por $b$ havas la kontraŭan direkton kaj tiu por
$c$ restas ĉe $i$. Ĉiu eliro uzas maksimume $T+1$ termojn. La
transporta respondo do havas grandon $O(V(T+1))$ kaj profundon
$O(log(T+2))$.

*Ĉiuj eniroj kun maksimume du partikloj.* Prenu ajnan validan komencan
fenestron kun maksimume du okupitaj trakbitoj kaj etendu ĝin per nuloj.
Se okazas unua netriviala kolizio, ambaŭ partikloj estas ĉe tiu ĉelo.
Ili foriras laŭ malsamaj trakoj kun malsamaj rapidoj el ${-1,0,1}$.
Iliaj liberaj vojoj poste monotone disiĝas, do dua kolizio ne povas okazi.
Netriviala kolizio inversigas ĝuste du bitojn rilate al la identeco antaŭ
la transporto. Transporto permutas la bitkoordinatojn, do la tuta konuso
enhavas maksimume du nenulajn restaĵbitojn. Du raŭndoj de tempa
bitriparo do prognozas $a_(0)(T)$ ĝuste sur ĉiu fenestro de la promeso.
Kun la respondo de libera transporto, la logspac-unuforma cirkvito
havas $O((T+1)^3)$ pordegojn kaj profundon $O(log(T+2))$.

*Profundo sub la dupartikla promeso.* Por $T>=1$ kaj ĉiu
$z in {-T,dots,-1}$, metu nur partiklon $b$ ĉe $T+2z$ kaj partiklon $c$
ĉe $z$. Ambaŭ ĉeloj estas en la komenca fenestro. Ili renkontiĝas ĉe $z$
je tempo $T+z$, kie la kolizio $011 -> 110$ lanĉas partiklon $a$, kiu
atingas la originon je tempo $T$. Forigi unu el la partikloj konservas la
promeson kaj nuligas la observon. Tio atestas po $T$ malsamajn esencajn
dratojn por $b$ kaj por $c$. Komparo de sola partiklo $a$ ĉe $-T$ kun
malplena eniro atestas unu plian draton. Ĉiu distinganta paro
kontentigas la promeson, do la retroa konuso de ĉiu ĝusta cirkvito kun
enira grado maksimume du devas enhavi ĉiujn $2T+1$ dratojn. La malsupra
baro estas $ell(2T+1)$. Kun la unuforma supra baro, la optimuma ordo
sub la promeso estas $Theta(log(T+1))$.

Por ajna entjero $h>=1$, metu unun nur ĉe $a_0$, $c_0$ kaj $c_(-h)$
kaj observu $a_(0)(2h)$. Je tempo nulo la stato $101$ ĉe la origino
fariĝas $011$ kaj sendas $b$ maldekstren. Je tempo $h$ la stato $011$
ĉe ĉelo $-h$ fariĝas $110$ kaj kreas dekstren moviĝantan $a$, kiu
atingas la originon je tempo $2h$. Intertempe ne okazas aliaj
netrivialaj kolizioj. La kvar nenulaj tutmondaj restaĵbitoj estas
$
  e^a_(0,1), quad e^b_(0,-1), quad e^a_(h,-h+1), quad e^c_(h,-h).
$
La lasta estas ekster la komuna konuso je statotempo $h+1$, kiam ĝia
radiuso estas $h-1$. La aliaj tri apartenas al la konuso. Forigi unu
el la du senmovaj partikloj nuligas la observitan biton, do ambaŭ
interagoj influas la observitan revenon. Tio donas aplikeblajn
interagantajn trajektoriojn ĉe arbitre grandaj observotempoj. La
atestilo limigas la kompleksecon de aplikeblo kaj de la kondiĉa observado.

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

*Linearaj referencoj kaj maldensaj trajektorioj.* La malkompono de
Moore inkluzivas ekzemplon de difektoprognozo @moore. Rowland kaj
Yassawi studis aŭtomatajn spactempajn diagramojn de skalaraj linearaj
ĉelaj aŭtomatoj @automatic-linear-ca. En @sparse-homogeneous-response
la duuma sekcio aplikata al la elementoj de fiksa transiga matrica
serio donas la drataron de la plena devigita respondo.
En SAT, malgrandaj krompordoj distingas utiligon de donita variablaro
disde ĝia serĉado @backdoors. Ĉi tie la kandidataj pozicioj estas
adresoj de restaĵbitoj sur trajektorio. Boyar, Find kaj Peralta
optimumigas linearajn partojn de fiksa cirkvito @boyar-low-depth,
dum la nenulaj restaĵoj ĉi tie povas ŝanĝiĝi laŭ la eniro.
Por frostiĝantaj retoj, baroj pri la alfabeta grando, grado kaj
arbolarĝo subtenas rapidan paralelan prognozon @freezing-parameters.
La nuna parametro nombras bitojn aŭ tavolojn kun diferenco rilate
al la elektita referenco.

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
La kompililo de ordigitaj resumoj realigas la adician kaj OR-prognozilojn.
Ĝi kalkulas la kostojn de pravalorizo, kunigo kaj ellego, kaj konservas
la blokordon ŝanĝante la krampadon.

Ĉiu fiksita regvorto elektas unu el kvar lokaj datumaj mapoj
$0$, $x_i$, $x_(i+1)$ kaj $x_i+x_(i+1)$. Post fiksado de la regvortoj
la datuma dinamiko estas unuflanka kaj lineara. La eniro estas eksplicita
fenestro kun longo lineara laŭ $T$, kaj la cirkvito povas kunligi
arbitrajn ĉelojn. La lokeco de la dinamiko kaj tiu de la prognozila
drataro estas apartaj kondiĉoj. La rezultoj uzas senliman drataron.
La kolizia profundobaro en @sparse-examples koncernas la promeson
pri maksimume du okupitaj bitoj en la komenca fenestro. La OR-ekzemplo
montras, ke malprofunda prognozo povas kunekzisti kun kvadrata restaĵpezo
rilate al la elektita referenco.

La akompana Lean-projekto formaligas tri sufiĉajn kriteriojn. A konstruas
prognozilon el kunmetaj cirkvitoj kun limigitaj rimedoj. B transdonas
P-malfacilecon de la problemo pri cirkvitvaloro, se disponeblas atestilo
pri logspaca simulado. Ekskludo el unuforma $"NC"$ per B supozas
$"P" != "NC"$ kaj koncernas kompleksecklason. C donas senkondiĉan
malsupran profundobaron laŭ la nombro de esencaj eniroj, kiel en la
modeloj ĉi tie. Ĉe fiksitaj enira grado, dimensio, radiuso kaj bitlarĝo,
lumkonuso de polinoma volumeno limigas la *nombran baron* de C al
$O(log(T+2))$. La efektiva prognoza profundo povas superi tiun baron.
La finia resumrekonilo kontrolas lokajn ekvaciojn por donitaj
taksilo kaj ŝablono. Ĝia konkludo uzas pruvon, kiu ligas la taksilon al
la prognoza tasko. Kolizio ekskludas sian kandidatan resumon, kaj la
larĝa baro koncernas sendependan resumon ĉe fiksa tranĉo. Ambaŭ rezultoj
koncernas la specifitan resuminterfacon. Por la familio kun fiksita
regado, la plenumebla
klasifikilo elektas branĉon per konstantecaj provoj sur finia alfabeto.

Lean kontrolas la finian konuson, rekonstruon, kontrolilon kaj
nombradon, kun baroj pri la nombro de pordegoj, profundo kaj bitlongo de
la seriigita priskribo, kaj kun unuformeco sub la aranĝaj hipotezoj. Lean
kontrolas la paralelajn riparcirkvitojn por bitoj kaj tavoloj, ilian
akcepton kaj kondiĉan eligon, la barojn por grando kaj profundo kaj
la kompletan logspacan seriigilon. Sub la unuformaj aranĝaj kaj blokaj
hipotezoj, fiksaj kaj logaritmaj nombroj de raŭndoj donas respektive
unuformajn $"NC"^1$ kaj $"NC"^2$. La pelataj respondoj por Pascal kaj
libera transporto havas kontrolitajn cirkvitojn kaj logspacajn generilojn.
Lean pruvas unuformecon de la kompletaj prognoziloj por OR kaj kolizio,
la rektan disjunkcion por OR kaj la precizajn koliziajn sojlojn de tri
bitaj raŭndoj kaj du tavolaj raŭndoj. Lean ankaŭ kontrolas la nombron
de densaj OR-restaĵoj kaj la riparan prognozilon por du partikloj.
La malsupra profundobaro sub la promeso sekvas en la teksto el la
eksplicitaj distingantaj paroj. La teksto pruvas la ĝeneralan
homogenan koeficientgenerilon per sekciaj operatoroj. Vidu @sparse-lean-map.

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

Ĉe trajektori-dependa prognozo, la plena loka kontrolo permesas al
malprofunda lineara respondo trakti maldensajn nelinearajn korektojn.
Nombrado utiligas malgrandan aron de eblaj pozicioj, dum la grando
de tempa riparo estas polinoma laŭ la konusvolumeno kaj la
korektobuĝeto. La reigebla kolizia familio montras aplikeblon ĉe
trajektorioj kun kaŭze ligitaj interagoj.

#heading(numbering: none)[Haveblo de la formaligo]

La fontoj en Lean kaj Typst kaj la kompilinstrukcioj troviĝas en la
#link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[projekta deponejo].
Uzu la deponejan revizion asociitan kun ĉi tiu PDF por trovi la deklarojn
en @lean-map.
La deponejo dokumentas la fiksitajn versiojn de Typst kaj la tiparojn
por rekonstrui la kvar eldonojn. Rulu #box[`./scripts/check.sh`] por la
strikta Lean-kompilo, kontrolo de importkovro, transitiva aksiomkontrolo
kaj regresprovoj.
La kontrolgvidilo distingas kompilajn rezultojn disde la revizio de modelaj
supozoj.
@lean-map listigas la deklarojn malantaŭ la ĉefaj rezultoj.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#set text(size: 10pt)
#set par(leading: 0.5em)
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

La tabelo havas $m^2(m+3)/2$ vicojn. Estas $O(m^2)$ nombriloj kun po
maksimume $m+1$ eniraj bitoj. La aranĝo uzas $O(m^3 log^3(m+1))$
pordegojn por fiksitaj gardoj. Pordegan rikordon indeksas stadio, bloko,
bitpozicio kaj loko en la ŝablono. Por paralelaj bankoj la serialigilo
nombras pli fruajn blokojn por trovi la dratan deŝovon. Identecaj pordegoj
$y and y$ donas sinsekvajn elirindeksojn. En ĉeno de larĝo $W$, post $G$
pordegoj kun $N$ ĉefaj eniroj, elirpozicio $a$ estas drato $N+G-W+a$.
La serialigilo tiel rekalkulas referencojn per logaritmlarĝaj nombriloj
kun fiksa nestada profundo kaj eligas la kodon laŭ la unume kodita longo.

#block[
#set text(size: 9.5pt)
#set par(leading: 0.42em, justify: false)
#heading(supplement: [Apendico])[Korespondo kun la Lean-deklaroj] <lean-map>

La vojoj sube estas relativaj al `PredictionDepth/`.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 2pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*Rezulto*], [*Lean-modulo kaj deklaro*]),
  table.hline(stroke: 0.4pt),
  [Iteracio kun fiksita regado],
  [`FrozenPascal/Semantics.lean` · `iterate_data`],
  [Fenestra interfaco],
  [`FrozenPascal/GuardRules.lean` · `rawSample_decodeRaw`],
  [Plenumebla klasifikilo],
  [`FrozenPascal/Classification.lean` · `classify`, `classify_eq_iff`],
  [Unuforma klasifiko],
  [`FrozenPascal/UniformClassification.lean` #linebreak()
   `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [Unuforma prognozilo],
  [`FrozenPascal/UniformPrediction.lean` #linebreak()
   `uniformGuardedPrediction_code_logspace` #linebreak() `uniformGuardedPrediction_depth`],
  [Kodkunmeto],
  [`Complexity/CodeLogspace.lean` · `compCode_logspace`],
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
    `reduction`, `prediction_correct`, `prediction_uniform`],
  [Kompililo de ordigitaj resumoj], [`Complexity/BlockSummary.lean` #linebreak()
    `compile_eval`, `compile_depth`, `compile_size`, `compile_code_logspace`],
  [Rekono kaj limoj de resumoj], [`BlockSummary.lean` #linebreak()
    `recognize?`, `findCollision?_sound`, `width_lower_bound`],
  [OR-instanco], [`ORAutomaton/Summary.lean` · `summaryFamily_uniform`],
  [Koeficientoj por adicia regado], [`AdditiveBranching.lean` · `trimmedParity_eq_sum`, `iterate_data`],
  [Baroj kaj unuformeco por adicia regado], [`AdditiveBranching/Summary.lean` #linebreak()
    `prediction_depth`, `prediction_size`, `predictionFamily_uniform` #linebreak()
    `AdditiveBranching/LowerBound.lean` · `prediction_depth_lower_bound`],
  [Kolizio por adicia regado], [`AdditiveBranching/Summary.lean` #linebreak()
    `frozenEndpointCollision`, `frozenEndpoint_noReadout`],
  table.hline(stroke: 0.7pt),
)
]

#block(breakable: false)[
#set text(size: 9.5pt)
#set par(leading: 0.42em, justify: false)
#heading(supplement: [Apendico])[Lean-deklaroj pri maldensaj korektoj] <sparse-lean-map>

La vojoj estas relativaj al `PredictionDepth/SparseCorrections/`.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 2pt),
  align: left,
  stroke: none,
  table.hline(stroke: 0.7pt),
  table.header([*Rezulto*], [*Lean-modulo kaj deklaro*]),
  table.hline(stroke: 0.4pt),
  [Komuna konuso kaj kontrolo], [`Semantics.lean` #linebreak() `Cone.finiteTrajectory_eq_restrict_iterate` #linebreak() `valid_iff_eq_actualResidual`],
  [Propagila formulo], [`Reconstruction.lean` #linebreak() `forcedTrajectory_eq_propagator_sum`],
  [Nombra kompililo], [`Compiler.lean` #linebreak() `compile_semantics` #linebreak() `compile_depth`, `compile_size` #linebreak() `compile_code_logspace`],
  [Longo de la seriigita priskribo], [`Description.lean` #linebreak() `compile_description_length_le`],
  [Unuforma nombrado], [`Certificate.lean` #linebreak() `Correct.unknown_mem_uniformNC_one` #linebreak() `Correct.scheduled_mem_uniformNC_one`],
  [Tempa bitriparo], [`Repair.lean` #linebreak() `repair_accept_iff`],
  [Tempa tavolriparo], [`LayerRepair.lean` #linebreak() `repairLayer_accept_iff`],
  [Paralelaj riparcirkvitoj], [`RepairCircuit.lean` #linebreak()
    `compileBits_correct`, `compileLayers_correct` #linebreak()
    `compile_size`, `compile_depth` #linebreak()
    `RepairCode.lean`, `compile_code_logspace`],
  [Unuforma riparo kaj sojloj], [`RepairUniform.lean` #linebreak()
    `fixedLanguage_mem_uniformNC_one` #linebreak()
    `logLanguage_mem_uniformNC_two` #linebreak()
    `RepairExamples.lean`, `example_repair_thresholds`],
  [Respondo de libera transporto], [`Streaming.lean` #linebreak() `forcedTrajectory_eq_characteristic` #linebreak()
    `StreamingCircuit.lean` #linebreak() `circuit_correct`, `circuit_code_logspace`],
  [Pelata respondo por Pascal], [`PascalResponse.lean` #linebreak()
    `circuit_correct`, `circuit_code_logspace` #linebreak()
    `circuit_size_quadratic`, `circuit_depth_logarithmic`],
  [Unuforma OR-prognozo], [`PascalOR.lean` #linebreak()
    `orPredictor_correct`, `orPrediction_mem_uniformNC_one` #linebreak()
    `orResidual_allOnes_card`],
  [Kolizia ekzemplo], [`Collision.lean` #linebreak() `step_reversible`, `returning_observation` #linebreak() `exampleResidual_card`],
  [Provoj por OR kaj tempo nulo], [`CompilerExamples.lean` #linebreak()
    `ORFixture.oneCorrection`, `ORFixture.code_agrees` #linebreak() `emptyHorizon_predicts`],
  [Unuforma kolizia prognozo], [`CollisionCertificate.lean` #linebreak()
    `sparsePrediction_mem_uniformNC_one` #linebreak() `example_accepts_and_predicts`],
  [Dupartikla prognozo], [`CollisionProperties.lean` #linebreak() `twoParticle_sparse` #linebreak()
    `RepairExamples.lean` #linebreak() `twoParticle_bitRepair_predicts`],
  table.hline(stroke: 0.7pt),
)
]

#bibliography("references.bib", style: "ieee", title: [Referencoj])
