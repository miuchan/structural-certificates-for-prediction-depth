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
  #text(size: 23pt, weight: "bold", title)
  #v(0.2em)
  #text(size: 13pt)[Fiksita kaj transportata regado en unuflankaj ĉelaj aŭtomatoj]
  #v(0.6em)
  #text(size: 12pt, author)
])

#pad(x: 8mm)[
#set text(size: 10.5pt)
*Resumo.* Ni klasifikas la prognozan profundon de unuflankaj ĉelaj aŭtomatoj,
kies fiksitaj regvortoj determinas, ĉu datumoj restas aŭ saltas en
ĝisdatigo super $bb(F)_2$. La eniro estas la eksplicita komenca luma
konuso kaj la eliro estas la datuma bito ĉe ĝia pinto. Por ĉiu fiksa regulo,
unu logspac-unuforma familio de cirkvitoj de De Morgan kun polinoma grando
realigas la koncernan supran profundobaron. La kazo kun variaj gardoj
havas profundon $Theta(log(T+1))$. Por la homogena Pascal-regulo, la
prognoza profundo egalas la nombron de unubitoj en la duuma prezento de $T$
ĝis faktoro tri. Ni analizas ankaŭ modelon kun transportata regado, en
kiu unu datuma vojo akumulas buleajn gardojn. Je pozitiva tempo egalaj
rapidoj de la rega kaj datuma trakoj donas profundon unu, kaj malsamaj
rapidoj donas precizan profundon $ceil(log_2(T+1))$. La finiaj rezultoj
sekvas el pruvoj en Lean 4 pri la dinamiko, cirkvita ĝusteco kaj malsupraj
baroj por limigita enira grado.

*Ŝlosilvortoj.* Ĉelaj aŭtomatoj, cirkvita profundo, logspaca unuformeco, Lean 4.
]

= Enkonduko

Algebra strukturo povas ebligi prognozon de la estonta stato de ĉela aŭtomato
per cirkvitoj multe pli malprofundaj ol laŭtavola simulado @moore.
Ni demandas, kiuj fiksitaj gardoj en unuflanka dutraka aŭtomato permesas
konstantan profundon kaj kiel la profundo dependas de la observa tempo.

Por fiksita regado, nombrado de vojoj donas unuforman konstruon de logaritma
profundo, kaj limigoj de la eniro donas malsuprajn barojn. La kvar rezultaj
kazoj inkluzivas homogenan regulon, kies profundo povas fali inter du
sinsekvaj tempoj (@frozen-classification). Por transportata regado, la relativa
rapido determinas kiom da malsamaj komencaj regbitoj aperas laŭ la datuma
vojo. Ekvilibra konjunkcio atingas la rezultan malsupran baron
(@transport-depth). Ambaŭ klasifikoj estas formaligitaj en Lean 4.

= Antaŭpreparoj

Loka regulo sur konfiguracioj super $bb(Z)$ estas iteraciata $T$ fojojn.
La celo estas la datuma bito ĉe la origino. Ĉiu modelo en la ĉefaj rezultoj
havas unuflankan ĝisdatigon de radiuso unu, do ĝia komenca fenestro konsistas
el la ĉeloj $0, dots, T$. Por fiksita regado la eniro enhavas $q(T+1)$
regbitojn sekvatajn de $T+1$ datumaj bitoj. La regvorta larĝo $q$ kaj la du
gardaj cirkvitoj estas fiksaj sendepende de $T$. La valida vortlongo
$n=(q+1)(T+1)$ unike determinas $T$. La lingvo konsistas el validaj vortoj
kies prognozita bito estas unu. Ĝi malakceptas ĉiujn aliajn longojn.

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
  buleaj pordegoj de enira grado maksimume du. La lingvo apartenas al
  logspac-unuforma $"NC"^0$ ĝuste kiam $h equiv 0$, aŭ kiam
  $h equiv 1$ kaj $s equiv 0$.
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

Por la supra baro, taksu la gardojn paralele kaj kalkulu la prefiksajn
pezojn $w_k$ kaj la produtojn $e_k$ el @frozen-iterate. La pezokalkula
cirkvito uzas ekvilibran redukton kun konservataj retenoj, sekvatan de
duuma adicio. Por $w_k>0$, la pareca testo por $M(w_k,T-k)$ kontrolas, ĉu
ĉiu unubito de $T-k$ aperas en $w_k+T-k-1$. Por $w_k=0$ validas la konvencio
pri nul partoj. La unuforma konstruo uzas tabelon de ĉi tiuj koeficientoj
generitan en logaritma spaco kaj elektas ilin laŭ la kalkulitaj prefiksaj
pezoj. Ekvilibra parecredukto kombinas la datumajn kontribuojn.
La profundobaro en @regimes enkalkulas la gardajn, aritmetikajn,
elektajn kaj reduktajn stadiojn.

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
konstantecon de la gardoj per prefiksa trairo de regvortoj. La provo
haltas ĉe la unua kontraŭekzemplo kaj en la plej malbona kazo povas viziti
$2^q$ vortojn.

= Transportata regado

Nun la rega trako havas propran dinamikon. Fiksu la rapidojn $u,v in {0,1}$
kaj la buleajn regan kaj datuman trakojn $(c_i,d_i)$. La sinkrona regulo
estas
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
datuma bito. Kun malsamaj rapidoj, la komencaj regindicoj estas
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
ĉelo povas cikli. La komparo identigas antaŭaĵojn por la ĉefaj ingrediencoj.
La preciza kvarbranĉa klasifiko kaj la transporta specialigo ankoraŭ
havas nedeterminitan literaturan prioritaton.

= Diskuto

#block(breakable: false)[
La klasifiko por fiksita regado validas kun eksplicite donita luma konuso
kaj fiksa finia paro de gardoj. La logaritma profundo estas mezurata laŭ
$n$, kiu kreskas lineare kun $T$. Kompakta priskribo de komenca stato
kun duuma tempo difinas apartan problemon. La rezulto pri unuformeco
koncernas la familion kun fiksita regado. La transporta rezulto koncernas
optimuman profundon ĉe ĉiu fenestrolongo. La cirkvitmodelo permesas
arbitran drataron. Kun nelimigita enira grado, la AND de transportata
regado takseblas en unu tavolo. Se anstataŭe ĉiu cirkvita tavolo havas
spacan drataran radiuson maksimume $r$, esenca koordinato je distanco
$T$ devigas $T <= d r$. Tiu aldona hipotezo estas uzata en la deponeja
geometria malsupra baro por la OR-aŭtomato. Kun arbitra drataro kaj enira
grado du tiu aparta ekzemplo havas precizan profundon $ell(2T+1)$.
]

*Kunmeta atestilo.* Estu $F$ evoluo, $I$ bitĉena malkodilo al ĝia statspaco
kaj $O$ observado. Supozu, ke buleaj cirkvitoj kun finiaj registroj
realigas pravalorizon, kunmeton laŭ la plenumata vojo kaj observadon.
Se iliaj profundoj estas $eta, delta, epsilon$, ripeta kvadratigo
produktas $O(F^T(I(x)))$ el $x$ kun profundo maksimume
$eta + 2 ell(T+1) delta + epsilon$. Aparta unuforma kompililo postulas
logspacajn generilojn por la primitivoj kaj enkalkulas kopiadon dum
normaligo. Ĝia profundobaro estas
$eta + 1 + 2 ell(T+1)(delta+1) + epsilon$, kun $delta$ kiel baro por
ambaŭ kunmetaj primitivoj. Membreco en $"NC"$ postulas plurlogaritman
baron laŭ la efektiva enirlongo.

*Simula atestilo.* Por specifita sistemo, logspaca transduktilo de
instancoj de la cirkvita valorproblemo al tutaj demandoj $1^T 0 x$,
kune kun pruvo de egala observado, faras la prognozan lingvon
P-malfacila sub logspacaj plur-al-unu-reduktoj @ladner. Polinomtempa
decidilo por la celo donas P-kompletecon. Sub la supozo
$"P" != "logspac-unuforma NC"$, kontrolita atestilo pri malfacileco
ekskludas la celon el tiu paralela klaso. Tiu konkludo rilatas al
klasmembreco. La literaturo donas konkretan P-kompletecan rezulton
por la aparta Regulo 110 @neary.

= Konkludo

La klasifiko por fiksita regado apartigas regulojn de konstanta prognoza
profundo de reguloj, kies profundo kreskas almenaŭ laŭ subsekvenco.
Inter la kreskantaj kazoj, la profilo de la homogena regulo sekvas la
unubitojn de la observa tempo. La transporta modelo izolas alian
mekanismon. Malsamaj komencaj regĉeloj akumuliĝas laŭ la datuma vojo nur
kiam la rapidoj malsamas. Ambaŭ klasifikoj sekvas el identigo de la
esencaj eniroj kaj konstruo de cirkvitoj, kiuj kombinas ilin kun la
bezonata profundo.

#heading(numbering: none)[Haveblo de la formaligo]

La Lean-formaligo, Typst-fonto kaj kompilinstrukcioj estas disponeblaj
en la #link("https://github.com/miuchan/structural-certificates-for-prediction-depth")[projekta deponejo].
`lean-toolchain` kaj `lake-manifest.json` fiksas la ilaron kaj la
dependecojn. Rulu #box[`./scripts/check.sh`] el la deponeja radiko por
kontroli la kovradon de la enirmodulo, kompili kun avertoj traktataj kiel
eraroj, kontroli transitivajn aksiomajn dependecojn kaj ruli la regresian
teston. @lean-map listigas la deklarojn respondajn al la ĉefaj rezultoj.

#counter(heading).update(0)
#set heading(numbering: "A.1")
#pagebreak(weak: true)
#heading(supplement: [Apendico])[Korespondo kun la Lean-deklaroj] <lean-map>

La vojoj sube estas relativaj al `PredictionDepth/`. La nomoj identigas
la maŝine kontrolitajn deklarojn subtenantajn la ĉefajn rezultojn.

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
  [Unuforma klasifiko],
  [`FrozenPascal/UniformClassification.lean` #linebreak()
   `uniform_depth_classification` #linebreak() `predictionLanguage_mem_uniformNC_zero_iff`],
  [Pascal-subteno],
  [`FrozenPascal/HomogeneousPascal.lean` #linebreak() `pascalSupport_card`],
  [Transportata regado],
  [`TransportedControl.lean` #linebreak()
   `iterate_data_true_iff`, `essential_prediction_iff` #linebreak()
   `exact_prediction_depth`, `constant_depth_iff`],
  [Kunmeta kriterio],
  [`EncodedPathComposition.lean` #linebreak()
   `EncodedPathImplementation.predictor_depth_le` #linebreak()
   `Complexity/UniformComposition.lean` #linebreak()
   `UniformRegisterWitness.depth_le_costs`],
  [Simula kriterio],
  [`Complexity/StandardHardness.lean` #linebreak()
   `SimulationWitness.prediction_P_complete` #linebreak()
   `Complexity/NCClosure.lean` #linebreak()
   `SimulationWitness.prediction_not_uniformNC`],
  table.hline(stroke: 0.7pt),
)

#bibliography("references.bib", style: "ieee", title: [Referencoj])
