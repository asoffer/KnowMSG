//DISPLAY CODES:
//0 there are no simple groups of order n
//1 there is a simple group of order n
//2 every group of order n is simple
//3 there are no (simple) groups of order n
function Technique(str, b, dc){
    if(b === undefined)
        b = false;
    if(dc === undefined)
        dc = 0;

    this.simpleType = b;
    this.test = function(n, p, np){ return false; }
    this.getProof = function(n, p, np){ return ""; }
    this.displayCode = dc;
}

Technique.prototype = {
    //try to eliminate the option, if you can, save the proof. return whether or not you did anything
    apply: function(n, p, np){
        if(this.simpleType)
            np = n;

        //if it's already been solved, don't try again
        if(np.proofComplete)
            return false;

        if(this.test(n, p, np)){
            np.proofComplete = true;
            np.proof = this.proof(n, p, np);

            n.workedOptions.pushBack(np);

            if(this.simpleType){
                var v = $("#inner_statement");
                switch(this.displayCode){
                    case 0:
                        v.html("<p>There are no simple groups of order $" + n + "=" + showFactorization(n) + "$.</p>");
                        break;
                    case 1:
                        v.html("<p>There is a simple group of order $" + n + "$.</p>");
                        break;
                    case 2:
                        v.html("<p>Every group of order $" + n + "$ is simple.</p>");
                        break;
                    case 3:
                        v.html("<p>There are no (simple) groups of order $" + n + "$.</p>");
                        break;
                    default:
                        v.html("<p>What the hell kind of question is that?.</p>");
                }

                n.proofShown = true;

            }
            return true;
        }

        return false;
    }
}

TechDP = new Technique("dihedral p test");
TechDP.test = function(n, p, np){
    return ((p.p + 1 == np) && (p.p * (np << 1) == n.n) && (p.p > 3));
}
TechDP.proof = function(n, p, np){
    return "<p>Since $G$ acts transitively on the " + sylow(p) + "s of $G$ by conjugation, we have a nontrivial map $\\phi:G\\to S_{" + np + "}$. If $P$ is a " + sylow(p) + " of $G$, since every element of the normalizer $N_G(P)$ fixes $P$, we in fact have a nontrivial map $\\overline\\phi=\\phi\\mid_{N_G(P)}:N_G(P)\\to S_{" + p + "}$. Since $\\left|N_G(P)\\right|=" + (p.p << 1) + "$, and the only groups of order $" + (p.p << 1) + "$ are $" + zmod(p.p << 1) + "$ and $D_{" + p + "}$, one of these must be a subgroup of $S_{" + p + "}$, which cannot be.</p>";
}

TechLI = new Technique("large intersection");
TechLI.test = function(n, p, np){
    if(p.pow == 1 || np % Math.pow(p.p, 2) == 1)
        return false;

    //we're looking for  divisors of p^a that are larger than p^(a+1)
    var f = n.kModM(0, Math.pow(p.p, p.pow));
    np.ptr = f.head.prev;

    while(np.ptr.data > Math.pow(p.p, p.pow + 1))
        np.ptr = np.ptr.prev;

    np.ptr = np.ptr.next;
    np.exp = "";
    if(p.pow > 2)
        np.exp = "^{" + (p.pow - 1) + "}";
    //now we know there are two sylow subgroups with large intersection.
    //both p and q are in the normalize of their intersection
    return (n.n/ np.ptr.data < n.divInject);
}
TechLI.proof = function(n, p, np){
    return "<p>Since $n_{" + p + "}\\not\\equiv 1(\\bmod" + p + "^2)$, there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + np.exp + "$.</p><p>However, $P\\cap Q$ is a $" + p + "$-subgroup of $P$ with index divisible by $" + p + "$, so $" + p + "$ divides $[N_P(P\\cap Q):P\\cap Q]$, meaning $N_P(P\\cap Q)=P$. This means, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + np.ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (n.n / np.ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (n.n / np.ptr.data) + "}$. Contradiction.</p>";
}

TechLAI = new Technique("large abelian intersection");
TechLAI.test = function(n, p, np){
    if(p.pow != 2 || n.countElements() + (Math.pow(p.p, 2) - 2) * np < n.n)
        return false;

    //we're looking for  divisors of p^a that ar larger than p^(a+1)
    var f = n.kModM(0, Math.pow(p.p, 2));
    np.ptr = f.head.prev;

    while(Math.pow(p.p, 3) < np.ptr.data)
        np.ptr = np.ptr.prev;

    np.ptr = np.ptr.next;

    return (n.n/np.ptr.data <= n.smartInject);

}
TechLAI.proof = function(n, p, np){
    var pf = "<p>Since the " + sylow("p") + " cannot intersect nontrivially for any prime $p$ such that $2\\nmid\\left|G\\right|$, at a minimum, we have ";

    var counter = 0;

    var ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
        if(ptr2.data.p != p.p && ptr2.data.pow == 1){
            pf += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data.toStringWithPower() + " - 1)=" + ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "$$\n";

            counter += ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1);
        }
        ptr2 = ptr2.next;
    }

    pf += "</p><p>Furthermore, for the primes $p$ such that $p^2$ divides $\\left|G\\right|$, there are at least two Sylow $p$-subgroups $P$ and $Q$. While they may have nontrivial intersection, if we are looking for a lower bound on the number of elements in " + sylow(p) + " of $G$, we must get $p^m$ elements from $P$ (where $p^m$ divides $\\left|G\\right|$, but $p^{m+1}$ does not), and at least one more element from $Q$. Thus, we get at very least";

    ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
        if(ptr2.data.p != p.p && ptr2.data.pow > 1){
            pf += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data + " - 1)=" + ptr2.data.smallestNP().np * (ptr2.data.p - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "^k$$\n";
            counter += ptr2.data.smallestNP().np * (ptr2.data.p - 1);
        }
        ptr2 = ptr2.next;
    }

    pf += "for a total of $" + counter + "$ elements.</p><p>Then the " + sylow(p) + " subgroups cannot have trivial intersection, lest there be another $" + np + "\\cdot(" + p + "^{" + p.pow + "} - 1)$ elements. So there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; " + p + "^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + "$.</p><p>Since every group of order $" + p.toStringWithPower() + "$ is abelian, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then the possibilities for $\\left|N_G(P\\cap Q)\\right|$ are $$";

    var pe = Math.pow(p.p, p.pow);
    var x = new Num(n.n/pe);
    x.computeFactorList();
    var l = x.factors.copy();
    while(l.first() < p.p)
        l.popFront();

    var ptr = l.head.next;
    while(ptr != l.head){
        ptr.data = ptr.data * pe;
        ptr = ptr.next;
    }

    var c = 0;
    var ptr = l.head.next;
    while(ptr != l.head){
        if(n.n/ptr.data < n.smartInject)
            ++c;
        ptr = ptr.next;
    }

    if(c == l.size)
        pf += toList(l, false).s + "$$ All $" + c + "$ of these are excluded";
    else 
        pf += toList(l, false).s + "$$ The last $" + c + "$ are excluded,";

    pf += " since in each case the index $[G:N_G(P\\cap Q)]$ would be less than $" + n.smartInject + "$. This is a problem because if we have a subgroup $H$ of $G$ with index less than $" + n.smartInject + "$, then $G$ acts by left multiplication on the left cosets, which induces a nontrivial map from $G$ into $S_{[G:H]}$, which we know cannot exist when $[G:H] &lt;" + n.smartInject + "$.";

    if(c == l.size)
        return pf + "Thus, there can be no simple groups of order $" + n.n + "$.</p>";

    //otherwise there is one more case FIXME
    return pf + "</p><p>Now we may assume $N_G(P\\cap Q)$ is a subgroup of $G$ of order $" + l.first() + "$. Since there are exactly $" + np.ptr.data + "$ elements which do not belong to " + sylow(n.n/np.ptr.data) + ", and $N_G(P\\cap Q)$ always conjugates to a subgroup of order $" + np.ptr.data + "$, it must always conjugate to itself, and hence must be normal. Contradiction.</p>";
}

//FINISH ME, WHEN DO I NEED WHAT FOR COUNTING
TechCount = new Technique("count");
TechCount.test = function(n, p, np){
    var ptr = n.primes.head.next;
    np.count = 0;

    while(ptr != n.primes.head){
        //for this prime, count with this np
        if(ptr.data == p){
            if(p.pow > 1)
                np.count += Math.pow(p.p, p.pow);
            else
                np.count += np * (p.p - 1);
        }
        else{
            if(ptr.data.pow > 1)
                np.count += Math.pow(ptr.data.p, ptr.data.pow);
            else
                np.count += ptr.data.smallestNP().np * (ptr.data.p - 1);
        }

        ptr = ptr.next;
    }

    return (np.count >= n);
}
TechCount.proof = function(n, p, np){
    var pf = "<p>If $p$ divides $\\left|G\\right|$, but $p^2$ does not, then the Sylow $p$-subgroups of $G$ are all isomorphic to $" + zmod("p") + "$, and therefore are required to have trivial intersection. That is, if $p^2\\nmid\\left|G\\right|$, we can conclude that $G$ contains $n_p\\cdot(p-1)$ elements of order $p$. We conclude that $G$ has a minimum of";

    var ptr = n.primes.head.next;
    while(ptr != n.primes.head){
        var myp = (ptr.data == p ? p : ptr.data);
        var mynp = (ptr.data == p ? np : ptr.data.smallestNP().np);

        if(ptr.data.pow == 1){
            pf += "$$" + mynp + "\\cdot(" + myp + " - 1)=" + mynp * (myp.p - 1) + "\\mbox{ elements of order }" + myp + "$$\n";
        }
        else{
            pf += "$$" + myp.toStringWithPower() + "= " + Math.pow(myp.p, myp.pow) + "\\mbox{ non-identity elements in " + sylow(myp) + "s }$$\n";
        }

        ptr = ptr.next;

    }

    pf += "<p>This constitutes $" + np.count + "$ elements in Sylow subgroups in a group of order $" + n + "$";

    if(np.count == n.n){
        pf += ", which leaves no room for an identity element";
    }
    return pf + ".</p>";
}

TechDNorm = new Technique("double normalizer");
TechDNorm.test = function(n, p, np){
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){

        //take a prime which divides n but not np
        if(np % np.ptr.data.p != 0 && np.ptr.data.p != p.p){

            var norm = new Num(n.n/np);
            norm.computeFactorList();

            return (norm.kModM(1, np.ptr.data.p).size == 1 &&
                    np.ptr.data.p != p &&
                    np.ptr.data.incompleteNPSize() == 1 &&
                    (n.n/np.ptr.data.smallestNP()) % Math.pow(p.p, p.pow) != 0);
        }

        np.ptr = np.ptr.next;
    }

    return false;

}

TechDNorm.proof = function(n, p, np){
    var exp = "";
    if(p.pow > 1)
        exp = "^{" + p.pow + "}";

    return "<p>Let $P_{" + p + "}$ be a " + sylow(p) + ". Then $N_G(P_{" + p + "})$ is a group of order $" + (n.n/np) + "$, and therefore has a " + sylow(np.ptr.data.p) + ", $P_{" + np.ptr.data.p + "}$. It is clear that $P_{" + np.ptr.data.p + "}$ is also a " + sylow(np.ptr.data.p) + " of $G$. Applying the Sylow counting technique to the group $N_G(P_{" + p + "})$, tells us that it contains exactly one " + sylow(np.ptr.data.p) + ", so $P_{" + np.ptr.data.p + "}\\lhd N_G(P_{" + p + "})$. Since every element of $P_{" + p + "}$ conjugates $P_{" + np.ptr.data.p + "}$ to itself, $P_{" + p + "}\\le N_G(P_{" + np.ptr.data.p + "})$. This means that $" + p + exp + "$ must divide the order of $N_G(P_{" + np.ptr.data.p + "})$. But we already know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + n + "/n_{" + np.ptr.data.p + "} = " + (n.n/np.ptr.data.smallestNP()) + "$, a contradiction.</p>";
}

TechSymDiv = new Technique("symmetric divisors");
TechSymDiv.test = function(n, p, np){
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){
        if(np.ptr.data.p <= np && (np.ptr.data.p << 1) > np){
            np.norm = n.n/np;
            np.other = factorial(np - np.ptr.data.p) * np.ptr.data.p * (np.ptr.data.p - 1);
            return (np.other % np.norm != 0) || (np.other == np.norm);
        }

        np.ptr = np.ptr.next;
    }
    return false
}
TechSymDiv.proof = function(n, p, np){
    pf = "<p>We know that $G$ acts on the " + sylow(p) + "s by conjugation, and this action gives rise to a nontrivial map $\\phi: G\\to S_{n_{" + p + "}}=S_{" + np + "}$. If $G$ is to be simple, $\\phi$ must be injective, so we can identify $G$ with a subgroup of $S_{" + np + "}$. Let $P_{" + np.ptr.data.p + "}$ be a " + sylow(np.ptr.data.p) + " of $G$. Since $" + np.ptr.data.p + "^2\\nmid\\left|S_{" + np + "}\\right|$, $P_{" + np.ptr.data.p + "}$ is also a " + sylow(np.ptr.data.p) + " of $S_{" + np + "}$. This means that $N_G(P_{" + np.ptr.data.p + "})\\le N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})$. We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + np + "}$ of order $" + np.ptr.data.p + "$. They come precisely from $" + np.ptr.data.p + "$-cycles, of which there are $$\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(np.ptr.data.p) + " of $S_{" + np.ptr.data.p + "}$, and each " + sylow(np.ptr.data.p) + " has exactly $" + (np.ptr.data.p - 1) + "$ elements of order $" + np.ptr.data.p + "$, there are $\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-2)!$ " + sylow(np.ptr.data.p) + "s.</p>"


        if(np.other % np.norm != 0){
            return pf + "<p>From the Sylow theorems, we know that $\\left|N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})\\right|=" + np.other + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $$N_G(P_{" + np.ptr.data.p + "})\\le N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "}),$$ which contradicts Lagrange's theorem.</p>";
        }

        else if(np.other == np.norm){
            return pf + "<p>From the Sylow theorems, we know that $\\left|N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})\\right|=" + np.other + "$. Moreover, we know that $G$ embeds into $A_{" + np + "}$, lest $G\\cap A_{" + np + "}\\lhd G$. So $N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "}) = " + (np.other/2) + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $$N_G(P_{" + np.ptr.data.p + "})\\le N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "}),$$ which contradicts Lagrange's theorem.</p>";
        }
}

TechTwoOdd = new Technique("2^1*m", true);
TechTwoOdd.test = function(n){
    return n % 4 == 2;
}
TechTwoOdd.proof = function(n){
    return "<p>Let $G$ be a group of order $" + n + "$. By Cauchy's theorem, $G$ has has an element $g$ of order $2$. As $G$ acts on itself by left multiplication, we have a map $\\phi: G\\to S_{\\left|G\\right|}$. This map by definition is injective, so $\\phi(G)\\cong G$. Since $\\phi(g)$ also has order 2, it must be the product of disjoint $2$-cycles. Furthermore, only the identity $\\phi(e)$ has any fixed points under this action, because $hx=x$, for $h,x\\in G$ means that $h=e$. Thus, $\\phi(g)$ must be the product of $" + (n >> 1) + "$ $2$-cycles. Since a $2$-cycle is an odd permutation, and $\\phi(g)$ is the product of an odd number of them, $\\phi(g)$ must be an odd permutation. That is, $\\phi(G)\\not\\subseteq A_{" + n + "}$. In particular, since $A_{" + n + "}\\lhd S_{" + n + "}$, we know that $\\phi(G)\\cap A_{" + n + "}\\lhd \\phi(G)$, meaning that $\\phi(G)$, and therefore $G$, is not simple.</p>";
}

TechNormInSym = new Technique("element size from Normalizer carefully");
TechNormInSym.test = function(n, p, np){
    var norm = new Num(n.n/np.np);

    //I can only solve the positive diophantine equation for two primes
    if(!norm.primes.size > 2 || !norm.mustBeCyclic())
        return;


    //its cyclic, so there's an element of order "norm."
    //find some np we know
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){
        var x = np.ptr.data.smallestNP();
        var y = n.n/x;


        var p1 = norm.primes.first().p;
        var p2 = norm.primes.last().p;
        //compute p1,p2 inverse mod the other
        var p1i = modInverse(p1,p2);
        var p2i = modInverse(p2,p1);

        //can i write it as a combination?
        if(p1i && p2i && np.ptr.data.np.size == 1 && y % norm.n != 0 && norm.n != x.np){

            //now we want to write
            //x.np = p1 * a + p2 * b
            var a = x.np * p1i % p2;
            var b = x.np * p2i % p1;
            if(a == 0)
                a = p2;
            if(b == 0)
                b = p1;

            var c = a * p1 + b * p2;
            if(c != x.np)
                return true;

        }

        np.ptr = np.ptr.next;
    }

}
TechNormInSym.proof = function(n, p, np){
    var x = new Num(n.n/np.np);
    return "<p>Let $P_{" + p + "}$ be a " + sylow(p) + ", and let $P_{" + np.ptr.data.p + "}$ be a " + sylow(np.ptr.data.p) + ". The normalizer $N_G(P_{" + p + "})$ has order $" + n.n/np.np + "$, and therefore must be cyclic, so we can pick $g\\in G$ to be an element of order $" + n.n/np.np + "$. Since $" + n.n/np.np + "$ does not divide $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + n + "/n_{" + np.ptr.data.p + "}=" + (n/np.ptr.data.smallestNP()) + "$, the group element $g$ cannot normalize $P_{" + np.ptr.data.p + "}$, nor any other " + sylow(np.ptr.data.p) + ". Thus, if we identify $g$ with its action on the $" + np.ptr.data.smallestNP() + "$ " + sylow(np.ptr.data.p) + ", we see that we have produced an element in $S_{" + np.ptr.data.smallestNP() + "}$ of order $" + n.n/np.np + "$ which has no fixed points.</p><p>Consider the cycle structure of $g$. If we say that $g$ has $a$ $" + x.primes.first().p + "$-cycles, and $b$ $" + x.primes.last().p + "$-cycles, we would need to find a solution to the Diophantine equation $$" + x.primes.first().p + "a+" + x.primes.last().p + "b=" + np.ptr.data.smallestNP() + ",$$ with $a,b&gt;0$. It is routine to check that no such solution exists.</p>";
}

TechOne = new Technique("is it one?", true, 1);
TechOne.test = function(n){ return n == 1 }
TechOne.proof = function(n){ return "<p>The trivial group is the only group on one element, and has no proper subgroup, let alone nontrivial normal ones, so it is vacuously simple.</p>"; }

TechSporadic = new Technique("is it a sporadic group", true, 1);
//TechSporadic.test = sporadicTest;

TechSimple = new Technique("classification theorem", true);
TechSimple.test = null;

TechPrimes = new Technique("prime or prime power", true, 2);
TechPrimes.test = function(n){ return (n.isPrime() || n.isPrimePower()); }
TechPrimes.proof = function(n){ return (n.isPrime() ? pf_prime(n.n)+(n.n == 2 ? "<center><div id = \"fsg\" class = \"ui-corner-all\"><iframe width=\"420\" height=\"315\" src=\"http://www.youtube.com/embed/UTby_e4-Rhg?autoplay=1\" frameborder=\"0\" allowfullscreen></iframe><br>Finite Simple Group (of Order Two)<br><a href = \"http://www.casa.org/node/2044\">Klein Four Group</a></div></center>" : "") : pf_prime_power(n.primes.first().p, n.n)); }

TechSylow = new Technique("does n_p only have one option", true);
TechSylow.test = function(n){
    n.ptr = n.primes.head.next
        while(n.ptr != n.primes.head){
            if(n.ptr.data.np.size == 1)
                return true;
            n.ptr = n.ptr.next;
        }

    return false;
}
TechSylow.proof = function(n){ return pf_one_mod_p(n, n.ptr.data); }

TechInjectBound = new Technique("bound the injection sizes", true);
TechInjectBound.test = function(n, b){
    n.ptr = n.primes.head.next;
    while(n.ptr != n.primes.head){
        if(n.ptr.data.np.last().np < b)
            return n.ptr.data;

        n.ptr = n.ptr.next;
    }

    return false;
}
TechInjectBound.proof = function(n){
    return pf_inject(n, n.ptr.data);
}

TechNC = new Technique("proof using NC and self-normalization");
TechNC.test= function(n, p, np){
    if(p.pow != 2 || n.primes.size != 2)
        return false;

    //show they intersect trivially
    //if not, normalizer has size at least p^3
    //find smallest factor larger than p^3
    var ptr = n.factors.head.next;
    while(ptr.data < Math.pow(p.p, 3) || ptr.data % p.p != 0){
        ptr = ptr.next;
    }
    n.k = ptr.data;

    //lower bound on the size of C_G(P_1 n P_2). size-order as well as div-order
    var k = ptr.data / (p - 1);

    while(k % p.p == 0)
        k /= p.p;

    n.x = new Num(k);
    n.x.computeFactorList();
    //there exists an element of this order
    var y = n.x.primes.first();

    n.ptr = n.primes.head.next;
    while(n.ptr != n.primes.head){
        n.j = n.n / n.ptr.data.smallestNP().np;
        if(n.j % (p.p * y.n) != 0 && n.ptr.data.np.size == 1)
            if(!findElementInAlt(p.p * y.n, n.ptr.data.np.first().np))
                return true;

        //check if i can find such an element
        n.ptr = n.ptr.next; 
    }

    return false;

}
TechNC.proof = function(n, p, np){
    return "<p>We first show that all " + sylow(p) + " intersect trivially. Suppose, by way of contradiction, that $P$ and $P'$ are distinct " + sylow(p) + " with nontrivial intersection $Q$. Then $\\left|Q\\right|=" + p + "$, and $Q\\lhd P$ and $Q\\lhd P'$. Thus, we can bound the size of the normalizer by $$\\left|N_G(P\\cap P')\\right|\\ge\\left|P\\cdot P'\\right|=\\frac{\\left|P\\right|\\cdot\\left|P'\\right|}{\\left|P\\cap P'\\right|}=" + p + "^3.$$ Thus, $\\left|N_G(Q)\\right|$ is at least $" + p + "^3$ and is divisible by $" + p + "$. The smallest such divisor of $" + n + "$ is $" + n.k + "$. Since $" + n + "$ is only divisible by two primes, every possible size of $N_G(Q)$ is divisible by $" + n.k + "$.</p><p>Recall that $Q\\cong\\mathbb Z/" + p.p + "\\mathbb Z$, so $\\mbox{Aut}(Q)" + (p.p == 2 ? "$ is trivial" : "\\cong\\mathbb Z/" + (p.p-1) +"\\mathbb Z$") + ". Since $N_G(Q)/C_G(Q)$ is isomorphic to a subgroup of $\\mbox{Aut}(Q)$ by the isomorphism $$g\\cdot C_G(Q)\\mapsto (x\\mapsto g^{-1}xg),$$ we deduce that $C_G(Q)$ is divisible by $" + n.k + "/" + (p.p - 1) + "=" + (n.k/(p.p-1)) + "$. In particular, if we take $x$, a generator for $Q$, and $y$, an element of order $" + n.x.primes.first().p + "$, we can see that $xy\\in C_G(Q)$ is an element of order $" + (p.p * n.x.primes.first().p) + "$ in $G$.</p><p>Now let $P_{" + n.ptr.data + "}$ denote a " + sylow(n.ptr.data.p) + ". Since $\\left|N_G(P_{" + n.ptr.data + "})\\right|=" + n.j + "$, our element $xy$ cannot normalize $P_{" + n.ptr.data + "}$. The action of $G$ by conjugation on the " + sylow(n.ptr.data) + " induces a nontrivial map $$\\phi:G\\to S_{" + n.ptr.data.np.first() +"}.$$ As before, $\\phi$ must be injective lest its kernel be a nontrivial normal subgroup of $G$. Thus, we can identify $G$ with its image under $\\phi$. Since $A_{" + n.ptr.data.np.first() + "}\\lhd S_{" + n.ptr.data.np.first() + "}$, we know that $G\\cap A_{" + n.ptr.data.np.first() + "}\\lhd G$, implying that in fact $G&lt;A_{" + n.ptr.data.np.first() + "}$. Because $N_G(P_2)$ is the subgroup that fixes a particular point, our element $xy$ of order $" + (p.p * n.x.primes.first().p) + "$ cannot have any fixed points, and must be an even permutation. We can enumerate all possible cycle structures for $xy$ to see that no such element exists.</p>";
}

TechNC2 = new Technique("proof using NC, number 2");
TechNC2.test = function(n, p, np){
    //n=420, p=7, np=15
    if(p.pow != 1)
        return false;

    var norm = n.n/np.np;
    var g = new Num(gcd(norm, p.p - 1));

    //okay, we probably killed some stuff here we know how to deal with, but this is just being safe.
    if(g.primes.size != 1)
        return false;

    //centralizer is at least this size. moreover, there is an element in the centralizer of this order
    n.cent = norm / Math.pow(g.primes.first().p, g.primes.first().pow);

    var c = new Num(n.cent);
    if(c.primes.size != 2)
        return false;

    n.ptr = n.primes.head.next;
    while(n.ptr != n.primes.head){
        n.j = n.n / n.ptr.data.smallestNP().np;
        if(n.j % n.cent != 0 && n.ptr.data.np.size == 1)
            if(!findElementInAlt(n.cent, n.ptr.data.np.first().np))
                return true;

        //check if i can find such an element
        n.ptr = n.ptr.next; 
    }

    return false;

}
TechNC2.proof = function(n, p, np){
    return "<p>Let $P$ be a " + sylow(p) + ". Recall that $\\mbox{Aut}(P)" + (p.p == 2 ? "$ is trivial" : "\\cong\\mathbb Z/" + (p.p-1) +"\\mathbb Z$") + ". Since $N_G(P)/C_G(P)$ is isomorphic to a subgroup of $\\mbox{Aut}(P)$ by the isomorphism $$g\\cdot C_G(P)\\mapsto (x\\mapsto g^{-1}xg),$$ we deduce that $C_G(P)$ is divisible by $" + n.cent + "$. In particular, if we take $x$, a generator for $P$, and $y$, an element of order $" + (n.cent/p.p) + "$, we can see that $xy\\in C_G(Q)$ is an element of order $" + n.cent + "$ in $G$.</p><p>Now let $P_{" + n.ptr.data + "}$ denote a " + sylow(n.ptr.data.p) + ". Since $\\left|N_G(P_{" + n.ptr.data + "})\\right|=" + n.j + "$, which is not divisible by $" + n.cent + "$, our element $xy$ cannot normalize $P_{" + n.ptr.data + "}$. The action of $G$ by conjugation on the " + sylow(n.ptr.data) + " induces a nontrivial map $$\\phi:G\\to S_{" + n.ptr.data.np.first() +"}.$$ As before, $\\phi$ must be injective lest its kernel be a nontrivial normal subgroup of $G$. Thus, we can identify $G$ with its image under $\\phi$. Since $A_{" + n.ptr.data.np.first() + "}\\lhd S_{" + n.ptr.data.np.first() + "}$, we know that $G\\cap A_{" + n.ptr.data.np.first() + "}\\lhd G$, implying that in fact $G&lt;A_{" + n.ptr.data.np.first() + "}$. Because $N_G(P_2)$ is the subgroup that fixes a particular point, our element $xy$ of order $" + n.cent + "$ cannot have any fixed points, and must be an even permutation. We can enumerate all possible cycle structures for $xy$ to see that no such element exists.</p>";
}

Tech720 = new Technique("720", true);
Tech720.test = function(n){ return n.n == 720; };
Tech720.proof = function(n){
    n.computeFactorList();
return "<div class=\"ui-state-highlight ui-corner-all\" style=\"margin-top: 0px; margin-bottom: 20px; padding: 1em .7em; font-size: 10pt;\"><span class=\"ui-icon ui-icon-info\" style=\"float: left; margin-right: .3em;\"></span><strong>Disclaimer:</strong> This proof is not my own work. It follows very closely the proof by Derrick Holt, found <a href = \"http://sci.tech-archive.net/Archive/sci.math/2006-12/msg07456.html\">here</a>.</div>" + pf_basic(n, false) + "<p></p><h6>Case $n_3=40$:</h6><p>Let $P$ be a " + sylow(3);
}
