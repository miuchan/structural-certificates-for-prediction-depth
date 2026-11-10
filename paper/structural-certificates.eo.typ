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
Por la homogena Pascal-regulo la profundo estas inter la nombro de
unubitoj de $T$ kaj trioblo de tiu nombro. Por struktura komparo ni
solvas apartan unuvojan modelon kun transportata regado. Je pozitiva
tempo ĝia profundo estas unu ĉe egalaj rapidoj kaj precize
$ceil(log_2(T+1))$ ĉe malsamaj rapidoj. Lean 4 kontrolas la klasifikon,
la ligon inter dinamiko kaj finia prognozo, kaj la cirkvitajn barojn kaj
generilojn por la reguloj kun fiksita regado.

*Ŝlosilvortoj.* Ĉelaj aŭtomatoj, cirkvita profundo, logspaca unuformeco, Lean 4.
]

= Enkonduko

Algebra strukturo povas ebligi prognozon de la estonta stato de ĉela aŭtomato
per cirkvitoj multe pli malprofundaj ol laŭtavola simulado @moore.
Ni demandas, kiuj fiksitaj gardoj en unuflanka dutraka aŭtomato permesas
konstantan profundon kaj kiel la profundo dependas de la observa tempo.

Nia ĉefa rezulto estas la kvarbranĉa klasifiko de reguloj kun fiksita
regado (@frozen-classification). Finia provo de la gardoj elektas branĉon.
Por ĉiu branĉo ni donas malsuprajn barojn je ĉiu tempo kaj unu efektivan
generilon, kies cirkvitoj atingas la koncernan supran baron je ĉiu tempo.
La homogena branĉo havas nemonotonan profundoprofilon, kiun regas la
unubitoj de la observa tempo. La ĉefa konstruo derivas prefiksajn
statistikojn el vojonombroj, kalkulas ilin paralele kaj uzas ilin por
elekti koeficientojn en logaritma profundo (@uniform-construction).
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
kaj konstantojn. Enira drato havas profundon nul. Pordegoj povas reuzi
elirojn kaj kunligi arbitrajn ĉelojn. La malsupraj baroj je ĉiu tempo
validas por arbitraj buleaj pordegoj de enira grado maksimume du en tiu
dratara modelo. Por fiksita regulo, $D(T)$ estas la minimuma profundo
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
      [$ell(T+1)$], [$104(ell(T+3)+1)+max(d_s,d_h)$],
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

Je $T=2^r-1$ la homogena regulo bezonas almenaŭ $r$ tavolojn, kaj tuj poste
je $T=2^r$ ekzistas cirkvito de profundo maksimume tri. Por $r>3$ tio estas
strikta falo de la minimuma profundo. La akompana klasifikilo kontrolas
konstantecon de la gardoj per prefiksa trairo de regvortoj. Lean pruvas,
ke ĝia liverita valoro estas ekvivalenta al la kondiĉo de la elektita
branĉo. La konstantecoprovo haltas ĉe la unua kontraŭekzemplo kaj en la
plej malbona kazo povas viziti $2^q$ vortojn.

== Unuforma prognoza cirkvito <uniform-construction>

Estu $m=T+1$. Post paralela taksado de ambaŭ gardoj ĉe ĉiuj ĉeloj,
la cirkvito tenas la gardbitojn kaj la datuman trakon en registro apud
$m$-bita tempoetikedo $tau$ kun unu aktiva bito. Komencante ĉe $u=0$, la
duumaj ciferoj de $T$ gvidas sinsekvon de duobligoj #box[$u -> 2u$] kaj
laŭvolaj pliigoj #box[$u -> u+1$]. Ĉiu operacio nur plusendas la etikedajn
dratojn kaj plenigas la mankantajn poziciojn per nuloj. La gardaj kaj
datumaj trakoj trairas senŝanĝe. Fine nur $tau_T$ estas unu.

*Paralelaj prefiksoj.* Por ĉiu $k$, nombri la $k+1$ restobitojn donas $w_k$,
kaj konjunkcio de la unuaj $k$ saltobitoj donas $e_k$. Ĉiuj prefiksoj
estas kalkulataj sendepende kaj paralele. Nombrilo de $a$ bitoj uzas
$b=ell(a+1)$ bitojn por ĉiu vorto kaj kompletigas la eniron ĝis $P=2^b$
paroj da vortoj. Paro reprezentas eniran biton aŭ nulon. Kunpremilo
reduktas tri vortojn al du. Por ĉiu bitpozicio la XOR de la tri bitoj
iras en la sumvorton, kaj ilia plimulta valoro iras en la sekvan
pozicion de la retenvorto. Tio konservas la sumon module de $2^b$ sen
retenpropagado ene de la rondo. Du kunpremiloj sinsekve kunigas du
parojn en unu. Post $b$ kunigrondoj la radika paro reprezentas la
tutan sumon. La fina adicio aplikas kunpremilon kun tria eniro nula
$b$ fojojn, ĉiufoje nuligante unu plian malaltan retenbiton.
Ĉar $a<2^b$, la rezulto estas la preciza nombro. La profundo estas
$O(b)$ ĉar ĉiu vojo trairas nur unu adicion kun retenpropagado.

*Elekto de koeficientoj.* Dum generado de la cirkvito oni listigas la
triopojn $(u,k,j)$ kun $0 <= u,k < m$ kaj $0 <= j <= k+1$. Estu
$C_(u,k,j)$ nulo se $u<k$, kaj $M(j,u-k) mod 2$ alie. Por $u>=k$ kaj
$j=0$ ĝi estas unu ĝuste kiam $u=k$. Por $j>0$ la Pascal-pareco dependas
de tio, ĉu ĉiu unubito de $u-k$ ankaŭ aperas en $j+u-k-1$. La generilo
povas trairi tiujn du entjerojn biton post bito. Ĉiu tabelvico kun
koeficiento unu testas $w_k=j$ per konjunkcio de kongruaj bitliteraloj
kaj kunigas la rezulton kun $tau_u$ per AND. Nula vico eligas konstanton.
Ĝuste unu kandidata paro $(u,j)$ povas kontentigi ambaŭ testojn. La XOR de
ĉiuj vicoj por ĉelo do estas $C_(T,k,w_k)$, la koeficiento en @frozen-sum.
La cirkvito unue reduktas laŭ $j$, poste laŭ $u$, kunigas ĉiun rezulton
kun $e_k$ kaj $x_k$ per AND, kaj fine kalkulas la XOR laŭ $k$. En ĉi tiu
konstruo ĉiu XOR-redukto legas la plej malaltan biton de nombrilo kun
konservataj retenoj.

#figure(
  table(
    columns: (2.1fr, 1fr, 1.15fr),
    inset: (x: 6pt, y: 4pt),
    align: left,
    stroke: none,
    table.hline(stroke: 0.7pt),
    table.header([*Stadio*], [*Paralelaj okazoj*], [*Profundobaro*]),
    table.hline(stroke: 0.4pt),
    [Taksado de gardoj], [$2m$], [$max(d_s,d_h)$],
    [Pravalorizo de registro kaj tempoetikedo], [Unu registro], [$6B$],
    [Nombroj de restoj kaj konjunkcioj de saltoj], [$m$ el ĉiu], [$22B$ kaj $5B$],
    [Testoj de koeficientaj vicoj], [$m^2(m+3)/2$], [$5B$],
    [Pareco laŭ $j$, poste laŭ $u$], [$m^2$, poste $m$], [Po $23B$],
    [AND kun saltprefikso kaj datumbito, poste fina pareco], [$m$, poste unu], [$2+23B$],
    table.hline(stroke: 0.7pt),
  ),
  caption: [Rimedoj de la generita prognoza cirkvito kun fiksita regado,
    kie $B=ell(T+3)+1$. La du prefiksaj kalkuloj okazas paralele.],
  kind: table,
  supplement: [Tabelo],
) <uniform-resources>

*Grando kaj generado.* La tabelo havas $m sum_(k=0)^(m-1) (k+2)$
vicojn, ĉiu kun $O(log^2(m+1))$ pordegoj en la regula konjunkcia aranĝo.
Kompletigita nombrilo havas
$O(a+1)$ blokojn de po $O(log(a+2))$ bitpozicioj en ĉiu el
$O(log(a+2))$ rondoj. Ĉiu bitpozicio uzas maksimume $O(log(a+2))$
pordegojn eĉ kiam la kunpremilo estas ripetata por ĉiu eliro. Estas
$O(m^2)$ nombriloj, inkluzive de tiuj por pareco, kun maksimume $m+1$
eniroj ĉiu. La gardokopioj, plusendo de la etikedo kaj konjunkcioj
ankaŭ restas ene de la rezulta baro de $O(m^3 log^3(m+1))$ pordegoj.
La profundo estas $O(log(m+1))$ ĉar nur fiksa nombro de logaritme
profundaj stadioj estas kunmetataj.
@depth-budget derivas la konstantojn de @regimes.

La seriigilo nombras la unuman enirlongon $n$, kontrolas divideblecon
per $q+1$ kaj ĉe validaj longoj kalkulas $m$ kaj $T$. Ĝi listigas la
tabelvicojn laŭ $(k,u,j)$ kaj trairas iliajn bitpoziciojn. La registro
havas kvar indeksitajn blokojn de larĝo $m$, por tempo, restado, salto
kaj datumoj. En nombrila rondo la bloko $e$ legas la blokojn $2e$ kaj
$2e+1$ de la antaŭa rondo, kun nuloj ekster la banko. Pordega rikordo
estas difinita de la rondo, bloko, bitpozicio kaj pozicio en la loka
ŝablono. Por seriigi paralelajn blokojn la generilo nombras antaŭajn
pordegojn kaj aldonas la rezultan delokigon al internaj referencoj.
En ĝenerala sinsekva kunmeto ĝi solvas eniran referencon per regenerado
de la koncerna antaŭa elirindico. Por sinsekvo de fiksa larĝo la
normaligo aldonas pordegon $y and y$ por ĉiu eliro, tiel ke la $W$
eliroj estas la lastaj $W$ dratoj en ordo. Kun $N$ komencaj eniroj
kaj $G$ jam eligitaj pordegoj, loka dratindico $i$ de la sekva
stadio fariĝas $N+G-W+i$. La nestoprofundo de la seriigiloj estas
fiksa. La iterindicoj, delokigoj kaj referencoj estas polinome baritaj
laŭ $n$, do fiksa nombro da nombriloj kaj provizoraj aritmetikaj valoroj
sufiĉas en $O(log(n+2))$ bitoj de laborspaco. La listoj de pordegoj kaj
eliroj estas eligataj sinsekve.

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

La paro $(u,v)=(0,0)$ estas la fiksita kazo sen salto kun restogardo $c_i$.
Ŝanĝi nur $u$ al unu donas logaritman profundon, kvankam la datumoj neniam
saltas. Por $(u,v)=(1,1)$ ambaŭ trakoj moviĝas, sed ilia egala rapido donas
konstantan profundon. Por ĉi tiu unuvoja regulo gravas la nombro de
malsamaj komencaj regbitoj laŭ la datuma vojo en ĝia moviĝanta referenca
sistemo. La kadro por tempovariaj koeficientoj en @moore kovras ĉi tiun
regulon. Ĝia sola vojo ebligas precize kalkuli la profundon.

= Rilata laboro

*Pascal-pareco kaj rapida prognozo.* La nombro $2^(p(T))$ de neparaj eroj
estas klasika. Rowland atribuas la duuman rezulton al Glaisher kaj
derivas ĝin el la teoremo de Lucas @rowland. La rapida prognozo de ĉelaj
aŭtomatoj en @moore jam uzas Pascal-koeficientojn por homogenaj adiciaj
reguloj. Ĝiaj modulaj adiciaj pordegoj povas havi nelimigitan eniran
gradon. La nuna Pascal-rezulto donas malsupran baron por limigita
enira grado je ĉiu tempo kaj kongruan profilon ĝis konstanta faktoro,
kun kontrolita unuforma generilo de cirkvitoj de De Morgan.

*Dependaj linearaj trakoj kaj koeficienta formulo.* La ĝenerala divida
metodo de Moore donas profundon $O(log^2(T+2))$ por prognozo de linearaj
stadioj dependantaj de tempo kaj spaco kun limigita enira grado @moore.
Fiksi la regadon kaj uzi la unuflankan regulon kun restado kaj salto
ebligas prefiksajn statistikojn kaj profundon $O(log(T+2))$ en ĉi tiu
specialigo. La koeficiento en @frozen-sum ankaŭ havas klasikan matrican
analogon. La unupaŝa datuma mapo estas supra dudiagonala operatoro sur la
koncerna finia fenestro. La formulo de Higham por funkcio de tia matrico
multiplikas la interajn eksterdiagonalajn elementojn per dividita diferenco
laŭ la diagonalaj elementoj @higham. Por la monomo $z^T$, la dividita
diferenco estas kompleta homogena polinomo de grado $T-k$. Kun diagonalaj
elementoj nul kaj unu ĝi nombras la samajn malfortajn komponaĵojn.
Oni povas specialigi la polinoman identecon al entjeraj nul-unu-elementoj
antaŭ redukto module de du, sen dividado en $bb(F)_2$.

*Maŝina kontrolo kaj la signifo de fiksado.* Silváši kaj Tomášek formaligis
limigitajn kradojn kaj komputeblajn ĉelajn aŭtomatojn en Lean @silvasi.
Tio estas precedenco por maŝine kontrolitaj ĉelaj aŭtomatoj. La nuna
formaligo kontrolas profundoklasifikon de regulfamilio kaj la efektivan
cirkvitgenerilon. La modelo de Ollinger kaj Theyssier kun frostiĝo
(*freezing*) postulas monotonan ordon por la tuta stato de ĉiu ĉelo
@ollinger. En @frozen-rule fiksa estas la regvorto, kaj la datumo ĉe
ĉelo povas cikli. La kontribuo ĉi tie estas la kombino de plenumebla
regulklasifikilo, profundobaroj je ĉiu tempo kaj kontrolita unuforma
generilo por la tuta regulfamilio kun fiksita regado. La preciza
kvarbranĉa klasifiko kaj la unuvoja transporta specialigo havas
nedeterminitan literaturan prioritaton.

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
grando, unuformeco kaj la baro je ĉiu tempo. La transporta teoremo
aparte establas optimuman profundon ĉe ĉiu fenestrolongo.

Ĉiu fiksita regvorto elektas unu el kvar lokaj datumaj mapoj
$0$, $x_i$, $x_(i+1)$ kaj $x_i+x_(i+1)$. Post fiksado de la regvortoj
la datuma dinamiko estas unuflanka kaj lineara. La eniro estas eksplicita
fenestro kun longo lineara laŭ $T$, kaj la cirkvito povas kunligi
arbitrajn ĉelojn. La akompana formaligo ankaŭ prezentas kriteriojn pri
kunmeto kaj simulado por aliaj modeloj. Ilia aplikado bezonas apartan
atestanton pri realigo aŭ redukto.

= Konkludo

La preciza kriterio por $"NC"^0$ kaj la Pascal-profilo montras malsamajn
manierojn, laŭ kiuj la prognoza profundo kun fiksita regado dependas de
tempo. Ĉe variaj gardoj la prefiksaj nombriloj ebligas elekti la
vojkoeficientojn en logaritma profundo, tiel ke la sama unuforma familio
atingas la supran baron ĉe ĉiu valida longo. La transporta regulo montras
alian mekanismon. Relativa moviĝo ŝanĝas profundon per la nombro de
komencaj regbitoj legitaj laŭ unu datuma vojo.

#heading(numbering: none)[Haveblo de la formaligo]

La formalaj rezultoj respondas al ĉi tiu #link("https://github.com/miuchan/structural-certificates-for-prediction-depth/tree/08e9aa3dfad7132226849b39386005397469d656")[fiksita revizio de la Lean-fonto].
La Typst-fonto kaj kompilinstrukcioj estas en la #link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[projekta deponejo].
Uzu la plenan Git-SHA asociitan kun la PDF por elekti la fontan revizion.
La deponejo dokumentas la fiksitajn versiojn de Typst kaj la tiparojn
por rekonstrui la kvar eldonojn. GitHub Actions kontrolas, ke ĉiuj kvar PDF-eldonoj rekonstrueblas el la elprenita revizio. Rulu
#box[`./scripts/check.sh`] por la strikta Lean-kompilo kaj aksiomkontrolo.
@lean-map listigas la deklarojn malantaŭ la ĉefaj rezultoj.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#pagebreak(weak: true)
#heading(supplement: [Apendico])[Kalkulo de la profundobaro] <depth-budget>

La normaligita nombrila arbo kostas maksimume $2+14b$ tavolojn,
inkluzive de pravalorizo kaj kopiado ĉe ĉiu kunigrondo. La fina adicio
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

#heading(supplement: [Apendico])[Korespondo kun la Lean-deklaroj] <lean-map>

La vojoj sube estas relativaj al `PredictionDepth/`.

#table(
  columns: (1fr, 2.55fr),
  inset: (x: 7pt, y: 5pt),
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
  [Pascal-subteno],
  [`FrozenPascal/HomogeneousPascal.lean` #linebreak() `pascalSupport_card`],
  [Transportata regado],
  [`TransportedControl.lean` #linebreak()
   `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
   `exact_prediction_depth`, `constant_depth_iff`],
  table.hline(stroke: 0.7pt),
)

#bibliography("references.bib", style: "ieee", title: [Referencoj])
