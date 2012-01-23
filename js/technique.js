function Technique(){
    this.test = function(n, p, np){ return false; }
    this.getProof = function(n, p, np){ return ""; }
}

Technique.prototype = {
    //try to eliminate the option, if you can, save the proof. return whether or not you did anything
    apply: function(n, p, np){
	//if it's already been solved, don't try again
	if(np.proofComplete)
	    return false;
	
	if(this.test(n, p, np)){
	    np.proofComplete = true;
	    np.proof = this.proof(n, p, np);
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
    this. normSize = new Num(n.n/np);
    this. maxCyclic = this.normSize.maxOrder();

    return ((new Num(this.maxCyclic)).sumOfPrimeDivisors() > np - 1);
}
TechElementSize.proof = function(n, p, np){
    return "<p>Let  $P_{" + p + "}$ be a " + sylow(p) + ". Then $N_G(P_{" + p + "})$ is a group of order $" + (n.n/np) + "$. Any group of order $" + (n.n/np) + "$ has a cyclic subgroup of order $" + this.maxCyclic + "$. However, the normalizer $N_G(P_{" + p + "})$ is the stabilizer $P_{" + p + "}$ under the action of conjugation on the " + sylow(p) + "s of $G$, so instead of only embedding inside $S_{" + np + "}$, we actually know that it embeds inside $S_{" + (np - 1) + "}$. But $S_{" + (np - 1) + "}$ has no cyclic subgroups of order $" + this.maxCyclic + "$.</p>";
}

TechLI = new Technique("large intersection");
TechLI.test = function(n, p, np){
    if(p.pow == 1 || np % Math.pow(p.p, 2) == 1)
	return false;

    //we're looking for  divisors of p^a that are larger than p^(a+1)
    var f = n.kModM(0, Math.pow(p.p, p.pow));
    this.ptr = f.head.prev;

    while(this.ptr.data > Math.pow(p.p, p.pow + 1))
	this.ptr = this.ptr.prev;

    this.ptr = this.ptr.next;
    this.exp = "";
    if(p.pow > 2)
	this.exp = "^{" + (p.pow + 1) + "}";
    //now we know there are two sylow subgroups with large intersection.
    //both p and q are in the normalize of their intersection
    return (n.n/ this.ptr.data < n.divInject);
}
TechLI.proof = function(n, p, np){
    return "<p>Since $n_{" + p + "}\\not\\equiv 1(\\bmod" + p + "^2)$, there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + this.exp + "$.</p><p>However, $P\\cap Q$ is a $" + p + "$-subgroup of $P$ with index divisible by $" + p + "$, so $" + p + "$ divides $[N_P(P\\cap Q):P\\cap Q]$, meaning $N_P(P\\cap Q)=P$. This means, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + this.ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (n.n / this.ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (n.n / this.ptr.data) + "}$. Contradiction.</p>";
}
