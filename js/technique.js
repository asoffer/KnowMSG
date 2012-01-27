function Technique(str, b){
    if(b === undefined)
	b = false;
    this.simpleType = b;
    this.test = function(n, p, np){ return false; }
    this.getProof = function(n, p, np){ return ""; }
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

	    if(this.simpleType){
		//FIXME do a message display as well
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


TechElementSize = new Technique("element size test");
TechElementSize.test = function(n, p, np){
    //look at the normalizer of a sylow p group. given it's size, we know that it has an element of some order maximal. maybe this is too big?
    np. normSize = new Num(n.n/np);
    np. maxCyclic = np.normSize.maxOrder();

    return ((new Num(np.maxCyclic)).sumOfPrimeDivisors() > np - 1);
}
TechElementSize.proof = function(n, p, np){
    return "<p>Let  $P_{" + p + "}$ be a " + sylow(p) + ". Then $N_G(P_{" + p + "})$ is a group of order $" + (n.n/np) + "$. Any group of order $" + (n.n/np) + "$ has a cyclic subgroup of order $" + np.maxCyclic + "$. However, the normalizer $N_G(P_{" + p + "})$ is the stabilizer $P_{" + p + "}$ under the action of conjugation on the " + sylow(p) + "s of $G$, so instead of only embedding inside $S_{" + np + "}$, we actually know that it embeds inside $S_{" + (np - 1) + "}$. But $S_{" + (np - 1) + "}$ has no cyclic subgroups of order $" + np.maxCyclic + "$.</p>";
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
	np.exp = "^{" + (p.pow + 1) + "}";
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

    return (n.n/np.ptr.data < n.divInject);

}
TechLAI.proof = function(n, p, np){
    var pf = "<p>Since the " + sylow("p") + " cannot intersect nontrivially for any prime $p$ such that $2\\nmid\\left|G\\right|$, at a minimum, we have ";

    var counter = 0;

    var ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
	if(ptr2.data.p != p.p && ptr2.data.pow == 1){
	    proof += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data.toStringWithPower() + " - 1)=" + ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "$$\n";

	    counter += ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1);
	}
	ptr2 = ptr2.next;
    }

    pf += "</p><p>Furthermore, for the primes $p$ such that $p^2$ divides $\\left|G\\right|$, there are at least two Sylow $p$-subgroups $P$ and $Q$. While they may have nontrivial intersection, if we are looking for a lower bound on the number of elements in Sylow $p$ subgroups of $G$, we must get $p^m$ elements from $P$ (where $p^m$ divides $\\left|G\\right|$, but $p^{m+1}$ does not), and at least one more element from $Q$. Thus, we get at very least";

    ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
	if(ptr2.data.p != p.p && ptr2.data.pow > 1){
	    proof += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data + " - 1)=" + ptr2.data.smallestNP().np * (ptr2.data.p - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "^k$$\n";
	    counter += ptr2.data.smallestNP().np * (ptr2.data.p - 1);
	}
	ptr2 = ptr2.next;
    }

    return pf + "for a total of $" + counter + "$ elements.</p><p>Then the " + sylow(p) + " subgroups cannot have trivial intersection, lest there be another $" + np + "\\cdot(" + p + "^{" + p.pow + "} - 1)$ elements. So there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + "$.</p><p>Since every group of order $" + p.toStringWithPower() + "$ is abelian, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + np.ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (n.n/np.ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (n.n/np.ptr.data) + "}$. Contradiction.</p>";

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
    if(np.ptr.data.pow > 1)
	exp = "^{" + np.ptr.data.pow + "}";

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
    pf = "<p>We know that $G$ acts on the " + sylow(p) + "s by conjugation, and this action gives rise to a nontrivial map $\\phi: G\\to S_{n_{" + p + "}}=S_{" + np + "}$. If $G$ is to be simple, $\\phi$ must be injective, so we can think of $G$ as being a subgroup of $S_{" + np + "}$. Let $P_{" + np.ptr.data.p + "}$ be a " + sylow(np.ptr.data.p) + " of $G$. Since $" + np.ptr.data.p + "^2\\nmid\\left|S_{" + np + "}\\right|$, $P_{" + np.ptr.data.p + "}$ is also a " + sylow(np.ptr.data.p) + " of $S_{" + np + "}$. This means that $N_G(P_{" + np.ptr.data.p + "})\\le N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})$.";
    
    if(np.other % np.norm != 0){
	return pf + "We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + np + "}$ of order $" + np.ptr.data.p + "$. They come precisely from $" + np.ptr.data.p + "$-cycles, of which there are $$\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(np.ptr.data.p) + " of $S_{" + np.ptr.data.p + "}$, and each " + sylow(np.ptr.data.p) + " has exactly $" + (np.ptr.data.p - 1) + "$ elements of order $" + np.ptr.data.p + "$, there are $\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-2)!$ " + sylow(np.ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{S_{" + np.ptr.data.p + "}}(P_{" + np.ptr.data.p + "})\\right|=" + np.other + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $N_G(P_{" + np.ptr.data.p + "})\\le N_{S_{" + np.ptr.data.p + "}}(P_{" + np.ptr.data.p + "})$, which contradicts Lagrange's theorem.</p>"
    }
    
    else if(np.other == np.norm){
	return pf + "We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + np + "}$ of order $" + np.ptr.data.p + "$. They come precisely from $" + np.ptr.data.p + "$-cycles, of which there are $$\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(np.ptr.data.p) + " of $S_{" + np.ptr.data.p + "}$, and each " + sylow(np.ptr.data.p) + " has exactly $" + (np.ptr.data.p - 1) + "$ elements of order $" + np.ptr.data.p + "$, there are $\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-2)!$ " + sylow(np.ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})\\right|=" + np.other + "$. Moreover, we know that $G$ embeds into $A_{" + np + "}$, lest $G\\cap A_{" + np + "}\\lhd G$. So $N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "}) = " + (np.other/2) + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $N_G(P_{" + np.ptr.data.p + "})\\le N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "})$, which contradicts Lagrange's theorem.</p>"
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
    var m = norm.maxOrder();

    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){
	var x = n.n/np.ptr.data.smallestNP();
	if(np.ptr.data.np.size == 1 && x % m != 0){
	    //can i write x as the sum of factors of m?
	    //FIXME

	    //at least for now, not even sure if this is legit
	    if(gcd(m, np.ptr.data.smallestNP()) == 1 || m > np.ptr.data.smallestNP())
		return true;
	}
	np.ptr = np.ptr.next;
    }

}
TechNormInSym.proof = function(n, p, np){
    return "BOOM";
}





//------------------------------

TechWacky = new Technique("wacky420");
TechWacky.test = function(n, p, np){
    var ptr = n.primes.head.next;
    while(ptr != n.primes.head){
	var norm = new Num(n.n/np.np);
	norm.computeFactorList();
	if(np.np % ptr.data.p == 0 && ptr.data.p != p.p && norm.kModM(1, ptr.data.p).size == 1)
	    return true;

	ptr = ptr.next;
    }

    return false;
}
TechWacky.proof = function(n, p, np){
    return "FIXME WACKY";
}

TechOne = new Technique("is it one?", true);
TechOne.test = function(n){ return n == 1 }
TechOne.proof = function(n){ return "<p>The trivial group is the only group on one element, and has no proper subgroup, let alone nontrivial normal ones, so it is vacuously simple.</p>"; }

TechSporadic = new Technique("is it a sporadic group", true);
//TechSporadic.test = sporadicTest;

TechSimple = new Technique("classification theorem", true);
TechSimple.test = null;

TechPrimes = new Technique("prime or prime power", true);
TechPrimes.test = function(n){ return (n.isPrime() || n.isPrimePower()); }
TechPrimes.proof = function(n){ return (n.isPrime() ? pf_prime(n.n) : pf_prime_power(n.primes.first().p, n.n)); }

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
