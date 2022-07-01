function sylow(p){
    return "Sylow $" + p + "$-subgroup";
}

function pf_let(n){
    return "Let $G$ be a group of order $" + n + "$. ";
}

pf_contradiction = "Assume for the sake of contradiction that $G$ is simple. ";

function pf_prime_power(p,ppow){
    return "<p>" + pf_let(ppow) + "By the class equation, $$\\left|G\\right|=\\left|Z(G)\\right|+\\sum_{g\\in O^*}[G:C_G(g)].$$ Since $\\left|G\\right|$ is divisible by $" + p + "$, as is the sum, it follows that $\\left|Z(G)\\right|$ is divisible by $" + p + "$. So either $Z(G)=G$, meaning $G$ is abelian and therefore not simple, or $Z(G)\\lhd G$.</p>"
}

function pf_one_mod_p(n,p){
    var textPow = "";
    if(p.pow > 1)
        textPow += "^{" + p.pow + "}";

    var index = new Num(n.n / Math.pow(p.p, p.pow));
    index.computeFactorList();

    return "<p>" + pf_let(n) + "From the Sylow theorems, we know that the number of " + sylow(p) + "s of $G$ must be congruent to $1$ modulo $" + p + "$ and divide the index $[G:P]$, where $P$ is any " + sylow(p) + " of $G$. We calculate the index as $[G:P]=" + n + "/" + p + textPow + "=" + index + "$. The divisors of $" + index + "$ are " + toEnglishCentered(index.factors, false, "f_" + index) + "of which, only $1$ is congruent to $1$ modulo $" + p + "$.</p><p>We also know from the Sylow theorems that the " + sylow(p) + "s of $G$ conjugate to each other. Since there is only one " + sylow(p) + ", $P$, for each $g\\in G$, $g^{-1}Pg=P$. That is, $P\\lhd G$, so there are no simple groups of order $" + n + "$.</p>";
}

function pf_div_inject(n){
    return "<p>" + pf_let(n) + pf_contradiction + "Notice that $" + n + "$ does not divide $" + (n.divInject - 1) + "!$, so any map from $G$ to $S_{" + (n.divInject - 1) + "}$ cannot be injective. Since for any map $\\psi:G\\to S_n$, we have that $\\ker\\psi\\unlhd G$, there can be no such non-trivial map for $n&lt;" + n.divInject + "$.</p>";
}

function pf_smart_inject(n){
    var ind = factorial(n.smartInject - 1)/n.n;
    var an = "A_{" + (n.smartInject - 1) + "}";
    var sn = "S_{" + (n.smartInject - 1) + "}";

    var pf = pf_div_inject(n) + "<p>Furthermore, if we have a map $\\psi:G\\to S_{" + (n.smartInject - 1) + "}$, it cannot be an injection. If it were, let $H=\\psi(G)\\le G$. Notice that $H$ has index $" + ind + "$ in $" + sn + "$.";

    if(ind % 2 == 1)
        pf += " Then $H$ cannot be a subgroup of $" + an + "$ lest it have index $" + (ind >> 1) + ".5$ in $" + an + "$.";
    else
        pf += " If $H\\le " + an + "$, then $[" + an + ":H]=" + (ind >> 1) + "$. Since, $" + an + "$ acts transitively on the cosets of $H$ in $" + an + "$, we have a nontrivial map $\\psi:" + an + "\\to S_{" + (ind >> 1) + "}$. The kernel of this map is a proper normal subgroup of $" + an + "$. Since this map cannot be injective for divisibility reasons, its existence contradicts the simplicity of $A_{" + (n.smartInject - 1) + "}$.";
    return pf + "</p><p>On the other hand, if $H\\not\\le " + an + "$, since $" + an + "\\lhd " + sn + "$, it follows that, $1 &lt; " + an + "\\cap H\\lhd " + sn + "\\cap H=H\\cong G$, contradicting the simplicity of $G$. Thus, any non-trivial map from $G$ into a symmetric group $S_n$ must in fact have $n\\ge" + n.smartInject + "$.</p>";
}

function pf_inject(n,p){
    var pf = "";
    var i;

    if(p.np.last().np >= n.divInject){
        pf += pf_smart_inject(n);
        i = n.smartInject;
    }
    else{
        pf += pf_div_inject(n);
        i = n.divInject;
    }

    var pow = "";
    if(p.pow != 1)
        pow = "^{" + p.pow + "}";
    var index = n.n/Math.pow(p.p, p.pow);

    return pf + "<p>From the Sylow theorems, we know that the number of Sylow " + p + "-subgroups of $G$ must be congruent to $1$ modulo " + p + " and divide the index $[G:P]$, where $P\\ $ is any " + sylow(p) + " of $G$. We calculate the index as $[G:P]=" + n + "/" + p.p + pow + "=" + index + "$. The divisors of $" + index + "$ which are congruent to $1$ modulo $" + p + "$ are " + toEnglishCentered(n.kModM(1,p.p), false, "CAN'T MATTER") + "</p><p>Since $G$ acts on the " + sylow(p) + "s transitively by conjugation, we have a nontrivial map $\\phi:G\\to S_{n_{" + p + "}}$ where $n_{" + p + "}$ denotes the number of " + sylow(p) + "s of $G$. But we know that $n_{" + p + "}\\le " + n.kModM(1,p.p).last() + "$. Since $G$ cannot inject into any permutation group $S_n$ for $n&lt;" + i + "$, we know that $\\ker\\phi\\ne 1$. Because the action of $G$ is transitive, $\\ker\\phi\\ne G$. Then we have the nontrivial normal subgroup $\\ker\\phi\\lhd G$. Contradiction.</p>";
}


function pf_basic(n, b){
    var pf = "";

    //b is a flag to tell us which injection proof to take
    if(b)
        pf += pf_smart_inject(n);
    else
        pf += pf_div_inject(n);

    pf += "<p>We also know from the Sylow theorems that for each prime $p$, the number of Sylow $p$-subgroups of $G$ must be congruent to $1$ modulo $p$ and divide the index $[G:P]$, where $P$ is any Sylow $p$-subgroup of $G$. Moreover, $G$ acts on the Sylow $p$-subgroups transitively by conjugation, so we get a map $\\phi_p:G\\to S_{n_p}$, where $n_p$ denotes the number of Sylow $p$-subgroups of $G$. Then we know that for each prime $p$ dividing $\\left|G\\right|$, $n_p\\ge";
    if(b)
        pf += n.smartInject;
    else
        pf += n.divInject;
    pf+= "$. Therefore," + sylowList(n);

    return pf;
}

function sylowList(n){
    var pf = "";
    var ptr = n.primes.head.next;

    while(ptr != n.primes.head.prev){
        var ioi = inOrIs("n_{" + ptr.data.p + "}", ptr.data.np, false);

        if(ioi.b)
            pf += "<span id = \"0:n_" + ptr.data.p + "\" class = \"list\" title = \"Expand this list\">$$" + ioi.s + ",$$</span>";
        else
            pf += "$$" + ioi.s + ",$$";
        ptr = ptr.next;
    }

    ioi = inOrIs("n_{" + ptr.data.p + "}", ptr.data.np, false);
    if(ioi.b)
        pf += "<span id = \0:n_" + ptr.data.p + "\" class = \"list\" title = \"Expand this list\">$$\\mbox{and }" + ioi.s + ".$$</span>";
    else
        pf += "$$\\mbox{and }" + ioi.s + ".$$</p>";

    return pf;
}
