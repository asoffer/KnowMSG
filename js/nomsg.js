//implementation of a doubly linked list (with only one sentinal)

function List(){
    this.head = {prev: null, next: null};
    this.head.next = this.head;
    this.head.prev = this.head;

    this.size = 0;
}

List.prototype = {
    toString: function(){
	if(this.size == 0)
	    return "[]";

	var str = "[" + this.head.next.data;
	var ptr = this.head.next;

	while(ptr.next != this.head){
	    ptr = ptr.next;
	    str += ", " + ptr.data;
	}

	return str + "]";
    },

    copy: function(){
	var l = new List();
	var ptr = this.head.next;
	while(ptr != this.head){
	    l.pushBack(ptr.data);
	    ptr = ptr.next;
	}

	return l;
    },

    //add data to the front of the list
    pushFront: function(d){
	++this.size;
	var n = {data: d, prev: this.head, next: this.head.next};
	this.head.next = n;
	n.next.prev = n;
    },


    //add data to the end of the list
    pushBack: function(d){
	++this.size;
	var n = {data: d, prev: this.head.prev, next: this.head};
	this.head.prev = n;
	n.prev.next = n;
    },

    //remove last item in the list and return it
    popFront: function(){
	if(this.size == 0)
	    return;

	d = this.head.next.data;
	this.head.next.next.prev = this.head;
	this.head.next = this.head.next.next;
	--this.size;

	return d;
    },

    //remove last item in the list and return it
    popBack: function(){
	if(this.size == 0)
	    return;

	d = this.head.prev.data;
	this.head.prev.prev.next = this.head;
	this.head.prev = this.head.prev.prev;
	--this.size;
	return d;
    },

    addBefore: function(d, fn){
	var ptr = this.head.next;
	if(ptr != this.head){
	    while(!fn(ptr.data)){
		ptr = ptr.next;
		if(ptr == this.head)
		    return this.pushBack(d);
	    }
	}
	++this.size;
	var n = {data: d, prev: ptr.prev, next: ptr};
	ptr.prev.next = n;
	n.next.prev = n;
    },

    //add data after the first element for which fn returns true
    //or just add at end
    addAfter: function(d, fn){
	var ptr = this.head.next;
	while(!fn(ptr.data)){
	    ptr = ptr.next;
	    if(ptr == this.head)
		return this.pushBack(d);
	}
	++this.size;
	var n = {data: d, prev: ptr, next: ptr.next};
	ptr.next = n;
	n.next.prev = n;
    },

    //the first element in the list
    first: function(){ return this.head.next.data; },

    //the last element in the list
    last: function(){ return this.head.prev.data; },

    //empty the list
    empty: function(){
	this.size = 0;
	this.head.next = this.head;
	this.head.prev = this.head;
    },

    //if data is in the list, remove it otherwise, return null
    remove: function(data){
	var ptr = this.head.next;

	while(ptr != this.head){
	    if(data.equals(ptr.data)){
		ptr.prev.next = ptr.next;
		ptr.next.prev = ptr.prev;

		--this.size;
		
		return data;
	    }

	    ptr = ptr.next;
	}
	return;
    },

    recomputeSize: function(){
	this.size = 0;

	var ptr = this.head.next;
	while(ptr != this.head){
	    ++this.size;
	    ptr = ptr.next;
	}
    },

    //call a function on every element of the list in order
    iterate: function(fn){
	var ptr = this.head.next;
	while(ptr != this.head){
	    fn(ptr.data);
	    ptr = ptr.next;
	}
    },

    //call a function on every element of the list in reverse order
    iterateReverse: function(fn){
	var ptr = this.head.prev;
	while(ptr != this.head){
	    fn(ptr.data)
	    ptr = ptr.prev;
	}
    },

    powerSet: function(){
	var l = new List();

	l.pushBack(new List());
	var ptr = this.head.next;
	while(ptr != this.head){
	    var sz = l.size;

	    for(var i = 0; i < sz; ++i){
		var x = l.popFront();
		var y = x.copy();
		y.pushBack(ptr.data);
		l.pushBack(x);
		l.pushBack(y);
	    }
	    ptr = ptr.next;
	}
	
	return l;
    }

};
function zmod(n){
    return "\\mathbb{Z}/" + n.toString() + "\\mathbb{Z}";
}

function sort(l){
    var l2 = new List();

    var ptr = l.head.next;

    while(ptr != l.head){
	l2.addBefore(ptr.data, function(x){ return (x >= ptr.data); });
	ptr = ptr.next;
    }

    return l2;
}

function factorial(n){
    if(n <= 0)
	return 1;
    return n * factorial(n - 1);
}

function triangle(n){
    return ((n * (n + 1))/2);
}

function gcd(a,b){
    if(a * b == 0)
	return a + b;

    if(a < b)
	return gcd(b,a);

    return gcd(b, a % b);
}

function toList(l,force){
    //return the string, but also a boolean telling us if the line is long
    var b = false;
    var s = "\\{";

    var ptr = l.head.next;
    var sz = 0;
    while(ptr != l.head){
	sz += ("" + ptr.data).length;

	if(sz > 40){
	    s += "$$ $$";
	    sz = 0;
	}

	s += ptr.data + ", ";
	ptr = ptr.next;
    }

    s = s.substr(0,s.lastIndexOf(",")) + "\\}";

    if(s.length > 80 && !force){
	s = "\\{" + l.first() + ",\\dots," + l.last() + "\\}";
	b = true;
    }

    return {s: s, b: b};
}

function inOrIs(e,l,force){
    //return the string, but also a boolean telling us if the line is long

    if(l.size == 1)
	return {s: (e + "=" + l.first()), b: false};

    var tl = toList(l, force);

    return {s: e + "\\in " + tl.s, b: tl.b};
}

function toEnglishCentered(l, force, toPass){
    if(l.size == 1)
	return "$$" + l.first() + "$$";
    if(l.size == 2)
	return "$$" + l.first() + "\\mbox{ and }" + l.last() + ",$$";

    var s = "$$";

    var ptr = l.head.next;

    var sz = 0;
    while(ptr != l.head.prev){
	sz += ("" + ptr.data).length;
	if(sz > 40){
	    s += "$$ $$";
	    sz = 0;
	}

	s += ptr.data + ", ";
	ptr = ptr.next;
    }

    s+= "\\mbox{ and }" + l.last() + "$$";
    if(s.length > 80){
	if(!force)
	    s = "<span id = \"0:" + toPass + "\" class = \"list\" title = \"Expand this list\">$$" + l.first() + ",\\dots," + l.last() + "$$</span>";
	else
	    s = "<span id = \"1:" + toPass + "\" class = \"list\" title = \"Expand this list\">" + s + "</span>";
    }


    return s;
}

function showFactorization(n){
    var str = "";

    var ptr = n.primes.head.next;
    while(ptr != n.primes.head){
	str += ptr.data.p;
	if(ptr.data.pow > 1)
	    str += "^{" + ptr.data.pow + "}"
	if(ptr.next != n.primes.head)
	    str += "\\cdot";
	ptr = ptr.next;
    }
    return str;
}

//returns the number of times n! is divisible by the prime p. assumes that p is prime.
function factorialDivisors(n,p){
    var m = n;
    var c = 0;
    while(m > 1){
	m /= p;
	c += Math.floor(m);
    }

    return c;
}


function sylow(p){
    return "Sylow $" + p + "$-subgroup";
}

function pf_let(n){
    return "Let $G$ be a group of order $" + n + "$. ";
}

pf_contradiction = "Assume for the sake of contradiction that $G$ is simple. ";

function pf_prime(p){
    return "<p>" + pf_let(p) + "Lagrange's theorem tells us that the order of every subgroup group of $G$ divides $" + p + "$. Since $" + p + "$ is prime, the only subgroups are the trivial group and $G$ itself, so these are the only normal subgroups as well. Hence, $G$ is simple.</p><p>Moreover, up to isomorphism, the only group of order $" + p + "$ is the cyclic group $" + zmod(p) + "$.</p>";
}

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
    pf+= "$. Therefore,";

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

//object used to hold information about classes of simple groups
function Simple(nm){
    this.name = nm;
    this.sym = null;
    this.fn = function(n,q){ return 1 };

    //are there any exceptions?
    this.exception = function(n,q){ return false};

    //this variable tells us if it has a determined factorization, or has a product with a variable number of terms
    this.determined = true;
    //if it is totally determined, we can use this to get a very good high guess on where to be looking for the product so we don't have to try lots of products
    this.logBound = 1;
    //if not, use this
    this.powSize = null;
}

Simple.prototype = {
    toString: function(){
	return "[" + this.name + " simple group class]";
    },

    isInstance: function(num){
	if(this.determined){
	    var q = Math.floor(Math.pow(num.n, 1/this.logBound)+1);

	    while(this.fn(0,q) > num){
		--q;
	    }

	    if(this.fn(0,q) == num && (new Num(q)).isPrimePower() && !this.exception(0,q)){
		return {q: q, n: 0};
	    }
	    else
		return false;
	}
	else if(this.powSize == -1){
	    var x = this.isThisSize(num);
	    if(!x)
		return false;
	    if(!this.exception(x.n, x.q))
		return x;
	    return false;
	}
	else{
	    var l = this.generatePotentialList(num);
	    var ptr = l.head.next;
	    while(ptr != l.head){
		if(this.fn(ptr.data.n, ptr.data.q) == num && (new Num(ptr.data.q)).isPrimePower() && !this.exception(ptr.data.n,ptr.data.q))
		    return ptr.data;
		ptr = ptr.next;
	    }
	    return false;

	}

    },

    //only used for undetermined guesses
    generatePotentialList: function(num){
	var ptr = num.primes.head.next;
	var potentials = new List();
	while(ptr != num.primes.head){
	    var pow = ptr.data.pow;
	    var n = 1;

	    while(this.powSize(n) <= pow){
		if(this.powSize(n) > 0 && pow % this.powSize(n) == 0){
		    potentials.pushBack({q: Math.pow(ptr.data.p, pow/this.powSize(n)), n: n});
		}
		++n;
	    }

	    ptr = ptr.next;
	}

	return potentials;

    },

}




var simpleA = new Simple("alternating group");
simpleA.sym = function(n,q){ return "A_{" + n + "}"; };
simpleA.determined = false;
simpleA.exception = function(n,q){ return n < 5; };
simpleA.powSize = -1;
simpleA.isThisSize = function(num){
    //fixme, this is really a very dumb way to do it. use newton's method with stirlings formula
    var x = 1;
    var c = 2;
    while(num.n > x){
	++c;
	x *= c;
    }

    if(num.n == x)
	return {n: c, q: 0};
    return false;
}

var simplePSL = new Simple("projective special linear group");
simplePSL.sym = function(n,q){ return "\\mbox{PSL}_{" + n + "}(" + q + ")"; };
simplePSL.determined = false;
simplePSL.exception = function(n,q){ return (n == 2 && (q == 2 || q == 3)); };
simplePSL.powSize = function(num){ return triangle(num - 1); };
simplePSL.fn = function(n,q){
    var x = 1;
    for(i = 2; i <= n; ++i)
	x *= Math.pow(q, i) - 1;

    return x * Math.pow(q, this.powSize(n))/gcd(n, q - 1);
}

var simpleO = new Simple("orthogonal group");
simpleO.sym = function(n,q){ return "B_{" + n + "}(" + q + ")"; };
simpleO.determined = false;
simpleO.exception = function(n,q){ return (((n == 2) && (q == 2)) || (n == 1)); };
simpleO.powSize = function(num){ return Math.pow(num, 2); };
simpleO.fn = function(n,q){

    var x = 1;
    for(i = 1; i <= n; ++i){
	x *= Math.pow(q, 2*i) - 1;
    }

    return x * Math.pow(q, this.powSize(n))/gcd(2, q - 1);
}

var simplePSp = new Simple("projective symplectic group");
simplePSp.sym = function(n,q){ return "\mbox{PS}p_{" + (2*n) + "}(" + q + ")"; };
simplePSp.determined = false;
simplePSp.exception = function(n,q){ return n < 3; };
simplePSp.powSize = function(num){ return num * num; };
simplePSp.fn = function(n,q){
    var x = 1;
    for(i = 1; i <= n; ++i){
	x *= Math.pow(q, 2 * i) - 1;
    }

    return x * Math.pow(q, this.powSize(n))/gcd(2, q - 1);
}

var simpleOp = new Simple("orthogonal group");
simpleOp.sym = function(n,q){ return "O_{" + (2*n) + "}^+(" + q + ")"; };
simpleOp.determined = false;
simpleOp.exception = function(n,q){ return n < 4; };
simpleOp.powSize = function(num){ return num * (num - 1); };
simpleOp.fn = function(n,q){
    var x = 1;
    for(i = 1; i < n; ++i){
	x *= Math.pow(q, i * 2) - 1;
    }

    return  x * Math.pow(q, this.powSize(n)) * (Math.pow(q, n) - 1)/gcd(4, Math.pow(q,n) - 1);
}

var simpleE6 = new Simple("exceptional Chevalley group");
simpleE6.sym = function(n,q){ return "E_6(" + q + ")"; };
simpleE6.fn = function(n,q){ return Math.pow(q, 36) *
			     (Math.pow(q, 12) - 1) *
			     (Math.pow(q, 9) - 1) *
			     (Math.pow(q, 8) - 1) *
			     (Math.pow(q, 6) - 1) *
			     (Math.pow(q, 5) - 1) *
			     (Math.pow(q, 2) - 1) /
			     gcd(3, q - 1);
			   };
simpleE6.logBound = 78;

var simpleE7 = new Simple();
simpleE7.name = "exceptional Chevalley group";
simpleE7.sym = function(n,q){ return "E_7(" + q + ")"; };
simpleE7.fn = function(n,q){ return Math.pow(q, 63) *
			     (Math.pow(q, 18) - 1) *
			     (Math.pow(q, 14) - 1) *
			     (Math.pow(q, 12) - 1) *
			     (Math.pow(q, 10) - 1) *
			     (Math.pow(q, 8) - 1) *
			     (Math.pow(q, 6) - 1) *
			     (Math.pow(q, 2) - 1) /
			     gcd(2, q - 1);
			   };
simpleE7.logBound = 133;

var simpleE8 = new Simple();
simpleE8.name = "exceptional Chevalley group";
simpleE8.sym = function(n,q){ return "E_8(" + q + ")"; };
simpleE8.fn = function(n,q){ return Math.pow(q, 120) *
			     (Math.pow(q, 30) - 1) *
			     (Math.pow(q, 24) - 1) *
			     (Math.pow(q, 20) - 1) *
			     (Math.pow(q, 18) - 1) *
			     (Math.pow(q, 14) - 1) *
			     (Math.pow(q, 12) - 1) *
			     (Math.pow(q, 8) - 1) *
			     (Math.pow(q, 2) - 1); };
simpleE8.logBound = 248;

var simpleF4 = new Simple();
simpleF4.name = "exceptional Chevalley group";
simpleF4.sym = function(n,q){ return "F_4(" + q + ")"; };
simpleF4.fn = function(n,q){ return Math.pow(q, 24) * (Math.pow(q, 12) - 1) * (Math.pow(q, 8) - 1) * (Math.pow(q, 6) - 1) * (Math.pow(q, 2) - 1); };
simpleF4.logBound = 52;

//FIXME the exception is when q=2, and then it has a simple subgroup of index 2. is this part of the classification, or are those cases found by something else? hopefully it's the latter, but i may need to fix that
var simpleG2 = new Simple();
simpleG2.name = "exceptional Chevalley group";
simpleG2.sym = function(n,q){ return "G_2(" + q + ")"; };
simpleG2.fn = function(n,q){ return Math.pow(q, 6) * (Math.pow(q, 6) - 1) * (Math.pow(q, 2) - 1); };
simpleG2.logBound = 14;
simpleG2.exception = function(n,q){ return (q == 2); };

var simple2A = new Simple("projective special unitary group");
simple2A.sym = function(n,q){ return "\\mbox{PSU}_{" + (n+1) + "}(" + q + ")"; };
simple2A.determined = false;
simple2A.exception = function(n,q){ return ((n == 2 && q == 2) || n ==1); };
simple2A.powSize = function(num){ return triangle(num); };
simple2A.fn = function(n,q){
    var x = 1;
    for(i = 1; i <= n; ++i)
	x *= Math.pow(q, i+1) + Math.pow(-1, i);

    return x * Math.pow(q, this.powSize(n))/gcd(n + 1, q + 1);
}

var simpleOm = new Simple("twisted Chevalley group");
simpleOm.sym = function(n,q){ return "\\mbox{O}_{" + (2*n) + "}^-(" + q + ")"; };
simpleOm.determined = false;
simpleOm.exception = function(n,q){ return n < 4; };
simpleOm.powSize = function(num){ return 2*triangle(num - 1); };
simpleOm.fn = function(n,q){
    
    var x = 1;
    for(i = 1; i < n; ++i)
	x *= Math.pow(q, 2*i) -1;

    return x * (Math.pow(q,n) + 1) * Math.pow(q, this.powSize(n))/gcd(4, Math.pow(q,n) + 1);
}

var simple2E6 = new Simple();
simple2E6.name = "Steinberg group";
simple2E6.sym = function(n,q){ return "{}^2E_6(" + q + "^2)"; };
simple2E6.fn = function(n,q){ return Math.pow(q, 36) *
			      (Math.pow(q, 12) - 1) *
			      (Math.pow(q, 9) + 1) *
			      (Math.pow(q, 8) - 1) *
			      (Math.pow(q, 6) - 1) *
			      (Math.pow(q, 5) + 1) *
			      (Math.pow(q, 2) - 1) /
			      gcd(3, q + 1); };
simple2E6.logBound = 78;

var simple3D4 = new Simple();
simple3D4.name = "Steinberg group";
simple3D4.sym = function(n,q){ return "{}^3D_4(" + q + "^3)"; };
simple3D4.fn = function(n,q){ return Math.pow(q, 12) *
			      (Math.pow(q, 6) - 1) *
			      (Math.pow(q, 2) - 1) *
			      (Math.pow(q, 8) + Math.pow(q,4) + 1); };

simple3D4.logBound = 28;

//these cases are odd. we use q when we mean to use n
var simpleSuz = new Simple();
simpleSuz.name = "Suzuki group";
simpleSuz.exception = function(n,q){ return this.nn < 1; };
simpleSuz.sym = function(n,q){ return "Sz(2^{" + this.nn + "})"; };
simpleSuz.fn = function(n,q){ 
    //for saving n;
    this.nn = Math.log(q)/Math.log(2);

    if(this.nn != Math.floor(this.nn))
	return -1;

    return Math.pow(q, 2) *
	(Math.pow(q, 2) + 1) *
	(q - 1);
};
simpleSuz.logBound = 5;

var simpleRee2 = new Simple();
simpleRee2.name = "Ree group";
simpleRee2.exception = function(n,q){ return this.nn < 1; };
simpleRee2.sym = function(n,q){ return "{}^2F_4(2^{" + this.nn + "})"; };
simpleRee2.fn = function(n,q){ 
    //for saving n;
    this.nn = Math.log(q)/Math.log(2);

    return Math.pow(q, 12) *
	(Math.pow(q, 6) + 1) *
	(Math.pow(q, 4) - 1) *
	(Math.pow(q, 3) + 1) *
	(q - 1);
};
simpleRee2.logBound = 26;

var simpleRee3 = new Simple();
simpleRee3.name = "Ree group";
simpleRee3.exception = function(n,q){ return this.nn < 1; };
simpleRee3.sym = function(n,q){ return "{}^2G_2(3^{" + this.nn + "})"; };
simpleRee3.fn = function(n,q){ 
    //for saving n;
    this.nn = Math.log(q)/Math.log(3);

    return Math.pow(q, 3) *
	(Math.pow(q, 3) + 1) *
	(q - 1);
};
simpleRee3.logBound = 7;

//to catch the derived subgroup of the 2F4 Ree groups
var simpleTits = new Simple();
simpleTits.name = "Tits group, ${}^2F_4(2)'$, which is the derived subgroup of (and has index $2$ in) the Ree group ${}^2F_4(2)$";
//simpleTits.sym = function(n,q){ return ""; };
simpleTits.determined = false;
simpleTits.powSize = -1;
simpleTits.isThisSize = function(num){
    if(num == 17971200)
	return {n: 0, q: 0};
}

//------------------------------

//we wont include primes, because they are taken care of elsewhere. they're much easier
var simpleArray = new Array(simpleA, simplePSL, simpleO, simplePSp, simpleOp, simpleE6, simpleE7, simpleE8, simpleF4, simpleG2, simple2A, simpleOm, simple2E6, simple3D4, simpleSuz, simpleRee2, simpleRee3, simpleTits);

function isSimple(n){
    var simpleList = new List();
    for(var i = 0; i < simpleArray.length; ++i){
	var x = simpleArray[i].isInstance(n);
	if(x){
	    var s = "he " + simpleArray[i].name;
	    if(simpleArray[i].sym != null)
		s += " $" + simpleArray[i].sym(x.n, x.q) + "$";
	    s += ".</p>";

	    simpleList.pushBack(s);
	}
    }

    if(simpleList.size == 0)
	return false;

    n.proofComplete = true;
    n.proofShown = true;

    $("#inner_statement").html("<p>There is a simple groups of order $" + n + "=" + showFactorization(n) + "$.</p>");

    this.proof = "";

    if(simpleList.size == 1){
	n.proof = "<p>Up to isomorphism, the only simple group of order $" + n + "$ is t" + simpleList.first();
	return true;
    }

    n.proof = "<p>The following are all of the simple groups of order $" + n + "$ up to isomorphism. Some of these groups may be isomorphic, but every simple group of order $" + n + "$ is isomorphic to at least one of the following:</p>";

    var ptr = simpleList.head.next;
    while(ptr != simpleList.head){
	n.proof += "<p>T" + ptr.data;

	ptr = ptr.next;
    }


    return true;
}

//------------------------------
var spor = new Array("7920", "95040", "443520", "10200960", "244823040", "175560", "604800", "50232960", "86775571046077562880", "4157776806543360000", "42305421312000", "495766656000", "64561751654400", "4089470473293004800", "1255205709190661721292800", "44352000", "898128000", "4030387200", "145926144000", "448345497600", "460815505920", "273030912000000", "51765179004000000", "90745943887872000", "4154781481226426191177580544000000", "808017424794512875886459904961710757005754368000000000");
var spor_sym = new Array("M_{11}","M_{12}", "M_{22}", "M_{23}", "M_{24}", "J_1", "J_2", "J_3", "J_4", "Co_1", "Co_2", "Co_3", "Fi_{22}", "Fi_{23}", "Fi_{24'}", "HS", "McL", "He", "Ru", "Suz", "O'N", "HN", "Ly", "Th", "B", "M");

var spor_name = new Array("a Mathieu group","a Mathieu group","a Mathieu group","a Mathieu group","a Mathieu group","a Janko group","a Janko group","a Janko group","a Janko group","a Conway group","a Conway group","a Conway group","a Fischer Group","a Fischer Group","a Fischer Group","the Higman-Sims group","the McLaughlin group","the Held group","the Rudvalis group","the Suzuki sporadic group","the O'Nan group","the Harada-Norton group","the Lyons group","the Thompson group","the Baby Monster group","the Fischer-Griess Monster, or the monster group");


function sporadicTest(num){
    for(var i = 0; i < spor.length; ++i){
	if((""+num.n) == spor[i]){
	    $("#inner_statement").html("<p>There exists a simple group of order $" + num +  "=" + showFactorization(num) + "$.</p>");

	    num.proof = "<p>In fact, the sporadic group $" + spor_sym[i] + "$, (" + spor_name[i] + ") has order $" + num.n + "$.</p>";
	    num.proofShown = true;
	    num.proofComplete = true;
	    return true;
	}
    }

    return false;
}
function Option(p,np){
    //pointers back
    this.p = p;
    this.n = p.n;

    this.np = np;

    this.proofComplete = false;
    this.proof = "";
}

Option.prototype = {
    toString: function(){
	return this.np.toString();
    },

    countTest: function(){
	if(this.proofComplete)
	    return;

	    
	var ptr = this.n.primes.head.next;
	var count = 0;

	while(ptr != this.n.primes.head){

	    //for this prime, count with this np
	    if(ptr.data == this.p){
		if(this.p.pow > 1)
		    count += Math.pow(this.p.p, this.p.pow);
		else
		    count += this.np * (this.p.p - 1);
	    }
	    else{
		if(ptr.data.pow > 1)
		    count += Math.pow(ptr.data.p, ptr.data.pow);
		else
		    count += ptr.data.np.first().np * (ptr.data.p - 1);
	    }

	    ptr = ptr.next;
	}

	//FINISH ME, WHEN DO I NEED WHAT FOR COUNTING?
	this.proof = "<p>If $p$ divides $\\left|G\\right|$, but $p^2$ does not, then the Sylow $p$-subgroups of $G$ are all isomorphic to $" + zmod("p") + "$, and therefore are required to have trivial intersection. That is, if $p^2\\nmid\\left|G\\right|$, we can conclude that $G$ contains $n_p\\cdot(p-1)$ elements of order $p$. We conclude that $G$ has a minimum of";

	var ptr = this.n.primes.head.next;
	while(ptr != this.n.primes.head){
	    var p = (ptr.data == this.p ? this.p : ptr.data);
	    var np = (ptr.data == this.p ? this.np : ptr.data.np.first().np);

	    if(ptr.data.pow == 1){
		this.proof += "$$" + np + "\\cdot(" + p + " - 1)=" + np * (p.p - 1) + "\\mbox{ elements of order }" + p + "$$\n";
	    }
	    else{
		this.proof += "$$" + p.toStringWithPower() + "= " + Math.pow(p.p, p.pow) + "\\mbox{ non-identity elements in " + sylow(p) + "s }$$\n";
	    }

	    ptr = ptr.next;
	    
	}

	if(count >= this.n.n){
	    this.proof += "<p>This constitutes $" + count + "$ elements in Sylow subgroups in a group of order $" + this.n + "$";

	    this.proofComplete = true;
	}

	if(count == this.n.n){
	    this.proof += ", which leaves no room for an identity element";
	}
	this.proof += ".</p>";
    },

    elementSizeTest: function(){
	if(this.proofComplete)
	    return;

	//look at the normalizer of a sylow p group. given it's size, we know that it has an element of some order maximal. maybe this is too big?
	var normSize = new Num(this.n.n/this.np);
	var maxCyclic = normSize.maxOrder();
	if((new Num(maxCyclic)).sumOfPrimeDivisors() > this.np - 1){
	    this.proofComplete = true;
	    this.proof = "<p>Let  $P_{" + this.p + "}$ be a " + sylow(this.p) + ". Then $N_G(P_{" + this.p + "})$ is a group of order $" + (this.n.n/this.np) + "$. Any group of order $" + (this.n.n/this.np) + "$ has a cyclic subgroup of order $" + maxCyclic + "$. However, the normalizer $N_G(P_{" + this.p + "})$ is the stabilizer $P_{" + this.p + "}$ under the action of conjugation on the " + sylow(this.p) + "s of $G$, so instead of only embedding inside $S_{" + this.np + "}$, we actually know that it embeds inside $S_{" + (this.np - 1) + "}$. But $S_{" + (this.np - 1) + "}$ has no cyclic subgroups of order $" + maxCyclic + "$.</p>";

	    return;
	}

    },

    symmetricDivisorTest: function(){
	if(this.proofComplete)
	    return;


	var ptr = this.n.primes.head.next;
	while(ptr != this.n.primes.head){
	    if(ptr.data.p <= this.np && (ptr.data.p << 1) > this.np){
		var norm = this.n.n/this.np;
		var other = factorial(this.np - ptr.data.p) * ptr.data.p * (ptr.data.p - 1);

		this.proof = "<p>We know that $G$ acts on the " + sylow(this.p) + "s by conjugation, and this action gives rise to a nontrivial map $\\phi: G\\to S_{n_{" + this.p + "}}=S_{" + this.np + "}$. If $G$ is to be simple, $\\phi$ must be injective, so we can think of $G$ as being a subgroup of $S_{" + this.np + "}$. Let $P_{" + ptr.data.p + "}$ be a " + sylow(ptr.data.p) + " of $G$. Since $" + ptr.data.p + "^2\\nmid\\left|S_{" + this.np + "}\\right|$, $P_{" + ptr.data.p + "}$ is also a " + sylow(ptr.data.p) + " of $S_{" + this.np + "}$. This means that $N_G(P_{" + ptr.data.p + "})\\le N_{S_{" + this.np + "}}(P_{" + ptr.data.p + "})$.";

		if(other % norm != 0){
		    this.proof += "We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + this.np + "}$ of order $" + ptr.data.p + "$. They come precisely from $" + ptr.data.p + "$-cycles, of which there are $$\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(ptr.data.p) + " of $S_{" + ptr.data.p + "}$, and each " + sylow(ptr.data.p) + " has exactly $" + (ptr.data.p - 1) + "$ elements of order $" + ptr.data.p + "$, there are $\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-2)!$ " + sylow(ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{S_{" + ptr.data.p + "}}(P_{" + ptr.data.p + "})\\right|=" + other + "$. We also know that $\\left|N_G(P_{" + ptr.data.p + "})\\right|=" + norm + "$. However, $N_G(P_{" + ptr.data.p + "})\\le N_{S_{" + ptr.data.p + "}}(P_{" + ptr.data.p + "})$, which contradicts Lagrange's theorem.</p>"
		    this.proofComplete = true;

		}

		else if(other == norm){
		    this.proof += "We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + this.np + "}$ of order $" + ptr.data.p + "$. They come precisely from $" + ptr.data.p + "$-cycles, of which there are $$\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(ptr.data.p) + " of $S_{" + ptr.data.p + "}$, and each " + sylow(ptr.data.p) + " has exactly $" + (ptr.data.p - 1) + "$ elements of order $" + ptr.data.p + "$, there are $\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-2)!$ " + sylow(ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{S_{" + this.np + "}}(P_{" + ptr.data.p + "})\\right|=" + other + "$. Moreover, we know that $G$ embeds into $A_{" + this.np + "}$, lest $G\\cap A_{" + this.np + "}\\lhd G$. So $N_{A_{" + this.np + "}}(P_{" + ptr.data.p + "}) = " + (other/2) + "$. We also know that $\\left|N_G(P_{" + ptr.data.p + "})\\right|=" + norm + "$. However, $N_G(P_{" + ptr.data.p + "})\\le N_{A_{" + this.np + "}}(P_{" + ptr.data.p + "})$, which contradicts Lagrange's theorem.</p>"
		    this.proofComplete = true;
		}
	    }

	    ptr = ptr.next;
	}

    },

    doubleNormalizerTest: function(){
	if(this.proofComplete)
	    return;

	var ptr = this.n.primes.head.next;
	while(ptr != this.n.primes.head){

	    //take a prime which divides n but not np
	    if(this.np % ptr.data.p != 0){

		var norm = new Num(this.n.n/this.np);
		norm.computeFactorList();

		if(norm.kModM(1, ptr.data.p).size == 1 &&
		   ptr.data.p != this.p &&
		   ptr.data.np.size == 1 &&
		   (this.n.n/ptr.data.np.first()) % Math.pow(this.p.p, this.p.pow) != 0){


		    var exp = "";
		    if(ptr.data.pow > 1)
			exp = "^{" + ptr.data.pow + "}";

		    this.proof = "<p>Let $P_{" + this.p + "}$ be a " + sylow(this.p) + ". Then $N_G(P_{" + this.p + "})$ is a group of order $" + (this.n.n/this.np) + "$, and therefore has a " + sylow(ptr.data.p) + ", $P_{" + ptr.data.p + "}$. It is clear that $P_{" + ptr.data.p + "}$ is also a " + sylow(ptr.data.p) + " of $G$. Applying the Sylow counting technique to the group $N_G(P_{" + this.p + "})$, tells us that it contains exactly one " + sylow(ptr.data.p) + ", so $P_{" + ptr.data.p + "}\\lhd N_G(P_{" + this.p + "})$. Since every element of $P_{" + this.p + "}$ conjugates $P_{" + ptr.data.p + "}$ to itself, $P_{" + this.p + "}\\le N_G(P_{" + ptr.data.p + "})$. This means that $" + this.p + exp + "$ must divide the order of $N_G(P_{" + ptr.data.p + "})$. But we already know that $\\left|N_G(P_{" + ptr.data.p + "})\\right|=" + this.n + "/n_{" + ptr.data.p + "} = " + (this.n.n/ptr.data.np.first()) + "$, a contradiction.</p>";

		    this.proofComplete = true;
		    return;
		}
	    }
	    ptr = ptr.next;
	}
    },

    largeIntersectionAbelianTest: function(){
	if(this.proofComplete)
	    return;

	
	if(this.p.pow != 2 || this.n.countElements() + (Math.pow(this.p.p, 2) - 2) * this.np < this.n.n)
	    return;

	//we're looking for  divisors of p^a that ar larger than p^(a+1)
	var f = this.n.kModM(0, Math.pow(this.p.p, 2));
	var ptr = f.head.prev;

	while(Math.pow(this.p.p, 3) < ptr.data)
	    ptr = ptr.prev;

	ptr = ptr.next;

	if(this.n.n/ptr.data < this.n.divInject){
	    this.proof = "<p>Since the " + sylow("p") + " cannot intersect nontrivially for any prime $p$ such that $2\\nmid\\left|G\\right|$, at a minimum, we have ";
	    var counter = 0;

	    var ptr2 = this.n.primes.head.next;
	    while(ptr2 != this.n.primes.head){
		if(ptr2.data.p != this.p.p && ptr2.data.pow == 1){
		    this.proof += "$$" + ptr2.data.np.first() + "\\cdot(" + ptr2.data.toStringWithPower() + " - 1)=" + ptr2.data.np.first().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "$$\n";

		    counter += ptr2.data.np.first().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1);
		}
		ptr2 = ptr2.next;
	    }

	    this.proof += "</p><p>Furthermore, for the primes $p$ such that $p^2$ divides $\\left|G\\right|$, there are at least two Sylow $p$-subgroups $P$ and $Q$. While they may have nontrivial intersection, if we are looking for a lower bound on the number of elements in Sylow $p$ subgroups of $G$, we must get $p^m$ elements from $P$ (where $p^m$ divides $\\left|G\\right|$, but $p^{m+1}$ does not), and at least one more element from $Q$. Thus, we get at very least";

	    ptr2 = this.n.primes.head.next;
	    while(ptr2 != this.n.primes.head){
		if(ptr2.data.p != this.p.p && ptr2.data.pow > 1){
		    this.proof += "$$" + ptr2.data.np.first() + "\\cdot(" + ptr2.data + " - 1)=" + ptr2.data.np.first().np * (ptr2.data.p - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "^k$$\n";
		    counter += ptr2.data.np.first().np * (ptr2.data.p - 1);
		}
		ptr2 = ptr2.next;
	    }


	    this.proof += "for a total of $" + counter + "$ elements.</p><p>Then the " + sylow(this.p) + " subgroups cannot have trivial intersection, lest there be another $" + this.np + "\\cdot(" + this.p + "^{" + this.p.pow + "} - 1)$ elements. So there must be two distinct " + sylow(this.p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + this.p + "$, and $P\\ne Q$, the index must be $" + this.p + "$. That is, $\\left|P\\cap Q\\right|=" + this.p + "$.</p><p>Since every group of order $" + this.p.toStringWithPower() + "$ is abelian, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + this.p + "^{" + (this.p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + this.p.p + "^{" + this.p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (this.n.n/ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (this.n.n/ptr.data) + "}$. Contradiction.</p>";
	    this.proofComplete = true;
	}
    },

    largeIntersectionTest: function(){
	if(this.proofComplete)
	    return;

	
	if(this.p.pow == 1 || this.np % Math.pow(this.p.p, 2) == 1)
	    return;

	//we're looking for  divisors of p^a that ar larger than p^(a+1)
	var f = this.n.kModM(0, Math.pow(this.p.p, this.p.pow));
	var ptr = f.head.prev;

	while(ptr.data > Math.pow(this.p.p, this.p.pow + 1))
	    ptr = ptr.prev;

	ptr = ptr.next;
	var exp = "";
	if(this.p.pow > 2)
	    exp = "^{" + (this.p.pow + 1) + "}";

	//now we know there are two sylow subgroups with large intersection.
	//both p and q are in the normalize of their intersection
	if(this.n.n/ ptr.data < this.n.divInject){
	    this.proof = "<p>Since $n_{" + this.p + "}\\not\\equiv 1(\\bmod" + this.p + "^2)$, there must be two distinct " + sylow(this.p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + this.p + "$, and $P\\ne Q$, the index must be $" + this.p + "$. That is, $\\left|P\\cap Q\\right|=" + this.p + exp + "$.</p><p>However, $P\\cap Q$ is a $" + this.p + "$-subgroup of $P$ with index divisible by $" + this.p + "$, so $" + this.p + "$ divides $[N_P(P\\cap Q):P\\cap Q]$, meaning $N_P(P\\cap Q)=P$. This means, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + this.p + "^{" + (this.p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + this.p.p + "^{" + this.p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (this.n.n / ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (this.n.n / ptr.data) + "}$. Contradiction.</p>";
	    this.proofComplete = true;
	    return;
	}

    },


    //maybe merge this with the element size test? it's kind of the same idea.
    dPTest: function(){
	if(this.proofComplete)
	    return;
	if(this.p.p + 1 == this.np && this.p.p * (this.np << 1) == this.n.n && this.p.p > 3){
	    this.proofComplete = true;
	    this.proof = "<p>Since $G$ acts transitively on the " + sylow(this.p) + "s of $G$ by conjugation, we have a nontrivial map $\\phi:G\\to S_{" + this.np + "}$. If $P$ is a " + sylow(this.p) + " of $G$, since every element of the normalizer $N_G(P)$ fixes $P$, we in fact have a nontrivial map $\\overline\\phi=\\phi\\mid_{N_G(P)}:N_G(P)\\to S_{" + this.p + "}$. Since $\\left|N_G(P)\\right|=" + (this.p.p << 1) + "$, and the only groups of order $" + (this.p.p << 1) + "$ are $" + zmod(this.p.p << 1) + "$ and $D_{" + this.p + "}$, one of these must be a subgroup of $S_{" + this.p + "}$, which cannot be.</p>";
	}
    }
}

function Prime(n,p,k){
    //pointer back
    this.n = n;

    this.p = p;

    this.pow = k;

    this.np = new List();
    this.proofCount = 0;
    this.proofComplete = false;
}

Prime.prototype = {
    toString: function(){
	return this.p.toString();
    },

    listPowers: function(){
	var l = new List();
	for(var i = 0; i <= this.pow; ++i){
	    l.pushBack(p.pow(i));
	}

	return l;
    },

    toStringWithPower: function(){
	if(this.pow == 1)
	    return this.p;

	return this.p + "^{" + this.pow + "}";
    },

    prove: function(){
	var ptr = this.np.head.next;

	while(ptr != this.np.head){
	    ptr.data.countTest();
	    ptr.data.elementSizeTest();
	    ptr.data.doubleNormalizerTest();
	    ptr.data.symmetricDivisorTest();
	    ptr.data.largeIntersectionAbelianTest();
	    ptr.data.largeIntersectionTest();
	    ptr.data.dPTest();
	    ptr = ptr.next;
	}

	//since we're deleting things later in the game, it's best to just check each time by iterating over this.np;
	ptr = this.np.head.next;
	while(ptr != this.np.head){
	    if(!ptr.data.proofComplete)
		return;

	    ptr = ptr.next;
	}

	this.proofComplete = true;
    },

    showProof: function(){
	var pf = "";

	//if we have a proof
	if(this.proofComplete){

	    //if there is only one, don't show the cases
	    if(this.np.size == 1)
		return this.np.first().proof;

	    //FIXME, lump cases together that can be
	    var ptr = this.np.head.next;

	    while(ptr != this.np.head){
		pf += "<h6>Case $n_{" + this.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

		ptr = ptr.next;
	    }

	    return pf;
	}

	else{
	    var str = ""
	    var ptr = this.np.head.next;
	    while(ptr != this.np.head){
		if(ptr.data.proofComplete)
		    str += "<h6>Case $n_{" + this.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

		ptr = ptr.next;
	    }

	    return str;
	}

    }

}

function Num(n){
    this.n = n;

    this.primes = new List();

    this.factors = new List();

    if(Math.log(this.n) > 40){
	this.proofComplete = true;
	this.proofShown = true;
	$("#inner_statement").html("<p>Unfortunately the input is to big for me to handle.</p>");
	$("#proof").html("<p></p>");
	return;
    }

    this.factor();

    this.divInject = Number.MAX_VALUE;
    this.smartInject = Number.MAX_VALUE;
    this.needSmart = false;

    //flags and vars for computing and showing proofs
    this.proofComplete = false;
    this.proof = "";
    this.proofShown = false;
}


Num.prototype = {
    toString: function(){
	return this.n;
    },

    factor: function(){
	if(this.primes.size != 0)
	    return;

	var m = this.n;
	var p = 2;
	while(m >= p){
	    var pow = 0;
	    while(m % p == 0){
		++pow;
		m /= p;
	    }

	    if(pow != 0){
		this.primes.pushBack(new Prime(this, p, pow));

	    }

	    ++p;
	}

    },

    computeFactorList: function(){
	if(this.factors.size != 0)
	    return;

	this.factors.pushBack(1);

	var primePtr = this.primes.head.next;
	while(primePtr != this.primes.head){
	    var ln = this.factors.size;
	    for(i = 0; i < ln; ++i){
		var x = this.factors.popFront();
		for(var j = 0; j <= primePtr.data.pow; ++j){
		    this.factors.pushBack( x * Math.pow(primePtr.data.p, j));
		}
	    }

	    primePtr = primePtr.next;
	}

	this.factors = sort(this.factors);

    },

    kModM: function(k,m){
	var l = new List();
	var ptr = this.factors.head.next;
	while(ptr != this.factors.head){
	    if(ptr.data % m ==k)
		l.pushBack(ptr.data);
	    ptr = ptr.next;
	}

	return l;
    },

    buildNP: function(){
	var ptr = this.primes.head.next;
	while(ptr != this.primes.head){
	    var l = this.kModM(1,ptr.data.p);

	    var lPtr = l.head.next;

	    while(lPtr != l.head){
		ptr.data.np.pushBack(new Option(ptr.data, lPtr.data));

		lPtr = lPtr.next;
	    }

	    ptr = ptr.next;
	}
    },

    isPrimePower: function(){
	return (this.primes.size == 1);
    },

    isPrime: function(){
	return (this.isPrimePower() && this.primes.first().pow == 1);
    },

    prove: function(){
	if(this.proofComplete)
	    return;

	if(this.n == 1){
	    this.proofComplete = true;
	    this.proof = "<p>The trivial group is the only group on one element, and has no proper subgroup, let alone nontrivial normal ones, so it is vacuously simple.</p>";
	    this.proofShown = true;
	    $("#inner_statement").html("<p>Every group of order $" + this.n + "$ is simple.</p>");
	    return;
	}

	//display taken care of inside
	if(sporadicTest(this))
	    return;

	if(this.isPrime()){
	    this.proofComplete = true;
	    this.proof = pf_prime(this.n);
	    this.proofShown = true;
	    $("#inner_statement").html("<p>Every group of order $" + this.n + "$ is simple.</p>");
	    return;
	}

	if(this.isPrimePower()){
	    this.proofComplete = true;
	    this.proof = pf_prime_power(this.primes.first().p, this.n);
	    this.proofShown = true;
	    $("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");
	    return;
	}

	//check if it's simple
	if(isSimple(this))
	    return;
	
	$("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");
	

	this.computeFactorList();

	this.buildNP();

	//iterate over primes and check if 1 is the only possible value for np
	var ptr = this.primes.head.next;
	while(ptr != this.primes.head){
	    if(ptr.data.np.size == 1){
		this.proofComplete = true;
		this.proof = pf_one_mod_p(this, ptr.data);
		this.proofShown = true;
		$("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");
		return;
	    }

	    ptr = ptr.next;
	}

	//compute the injections

	this.computeInjections();


	var p = this.somethingLessThanInject(this.divInject);
	if(p){
	    this.proofComplete = true;
	    this.proof = pf_inject(this, p);
	    this.proofShown = true;
	    $("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");
	    return;
	}

	p = this.somethingLessThanInject(this.smartInject);
	
	if((this.smartInject > 4 || factorial(this.smartInject)/this.n < 3) && p){
	    this.proofComplete = true;
	    this.proof = pf_inject(this, p);
	    this.proofShown = true;
	    $("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");
	    return;
	}


	//knock off nps too small for a div injection. if we need to
	//do smart injection too. there's a question about wehether
	//this is simpler than some of the other arguments, but it's
	//much easier to do this check once than have some wacky
	//ordering and have to check it 3 different times.
	ptr = this.primes.head.next;
	while(ptr != this.primes.head){
	    while(ptr.data.np.first().np < this.divInject)
		ptr.data.np.popFront();
	    while(ptr.data.np.first().np < this.smartInject){
		this.needSmart = true;
		ptr.data.np.popFront();
	    }
	    ptr = ptr.next;
	}

	ptr = this.primes.head.prev;
	while(ptr != this.primes.head){
	    ptr.data.prove();
	    if(ptr.data.proofComplete){
		this.proofComplete = true;
		return;
	    }
	    ptr = ptr.prev;
	}

    },

    countElements: function(){
	var c = 0;
	var ptr = this.primes.head.next;
	while(ptr != this.primes.head){
	    if(ptr.data.pow == 1){
		c += ptr.data.np.first().np * (ptr.data.p - 1);
	    }
	    else
		c += Math.pow(ptr.data.p, ptr.data.pow);
	    ptr = ptr.next;
	}

	return c;
    },

    showProof: function(){
	if(this.proofShown)
	    return this.proof;

	var ptr = this.primes.head.prev;

	if(this.proofComplete){
	    //if we actually have a proof
	    while(!ptr.data.proofComplete)
		ptr = ptr.prev;

	    while(ptr.data.np.first().np < this.smartInject)
		ptr.data.np.popFront();

	    this.proof += pf_basic(this, this.needSmart) + ptr.data.showProof();

	}
	else{
	    this.proof = "<p>While I cannot find an elementary proof, "
	    //try burnside
	    if(this.primes.size == 2)
		this.proof += "Burnside's Theorem tells us that for primes $p$ and $q$, and natural numbers $a$ and $b$, groups of order $p^a\\cdot q^b$ are solvable. The only solvable groups which are simple are the cyclic groups of prime order. Since $" + this.n + "$ is not prime, no group of order $" + this.n + "$ can be simple.";

	    //try feit-thompson
	    else if(this.n % 2 == 1)
		this.proof += "the Feit-Thompson Theorem says that all groups of odd order are solvable. The only solvable groups which are simple are the cyclic groups of prime order. Since $" + this.n + "$ is not prime, no group of order $" + this.n + "$ can be simple.";

	    //use the classification
	    else
		this.proof += "the classification theorem for finite simple groups tells us the possible sizes of finite simple groups, to which $" + this.n + "$ does not belong.";

	    var email = "asoffer";
	    this.proof += " Below is all of the information which I could figure out in a proof-like format. Do you know an elementary technique that would solve this case? <a href = \"mailto:" + email + "@math.ucla.edu\">Let me know</a>!</p><hr>";
	    var ptr = this.primes.head.next;

	    this.proof += pf_basic(this, this.divInject != this.smartInject);

	    var str = "";
	    while(ptr != this.primes.head){
		str += ptr.data.showProof();

		ptr = ptr.next;
	    }
	    if(str != ""){
		//then add on the final results if anything was added on
		this.proof += str;// + "FINISH ME";
	    }

	}

	this.proofShown = true;
	return this.proof;
    },

    somethingLessThanInject: function(inj){
	var ptr = this.primes.head.next;
	while(ptr != this.primes.head){
	    if(ptr.data.np.last().np < inj)
		return ptr.data;

	    ptr = ptr.next;
	}

	return false;
    },

    computeInjections: function(){
	var m = 0;
	var ptr = this.primes.head.next;

	while(ptr != this.primes.head){
	    var guess = Math.floor(ptr.data.pow / (ptr.data.p - 1));

	    while(factorialDivisors(guess, ptr.data.p) <= ptr.data.pow)
		++guess;

	    if(factorialDivisors(guess - 1, ptr.data.p) == ptr.data.pow)
		guess -= ptr.data.p;

	    if(m < guess)
		m = guess;

	    ptr = ptr.next;
	}
	this.divInject = m;


	//WARNING: this is for test that create a normal subgroup of A_n.
	//the method to calculate this.smartInject is sufficient, but we
	//do not guarantee that n > 4 (i.e., we don't guarantee A_n is
	//simple).

	var leftOver = 1;
	var i = 1;
	var n = this.n;
	while(n > 1 && leftOver < (this.divInject << 1)){
	    var g = gcd(n, i);
	    n /= g;
	    leftOver *= i/g;
	    ++i;
	}

	this.smartInject = this.divInject;

	if(leftOver >= (this.divInject << 1))
	    return;

	++this.smartInject;
	if(leftOver == 1)
	    ++this.smartInject;

    },

    sumOfPrimeDivisors: function(){
	var s = 0;
	var ptr = this.primes.head.next;

	while(ptr != this.primes.head){
	    s += ptr.data.p;
	    ptr = ptr.next;
	}

	return s;
    },

    maxOrder: function(){
	//iterate over the powerset
	var p = this.primes.powerSet();
	var ptr = p.head.next;
	var n;
	var m = -1;
	while(ptr != p.head){
	    //make a num which is the product of the primes
	    n = 1;

	    var ptr2 = ptr.data.head.next;
	    while(ptr2 != ptr.data.head){
		n *= ptr2.data.p;
		ptr2 = ptr2.next;
	    }
	    var x = new Num(n);
	    x.computeFactorList();
	    if(x.mustBeCyclic() && n > m)
		m = n;

	    ptr = ptr.next;
	}

	return m;

    },

    mustBeCyclic: function(){
	var ptr = this.primes.head.next;

	while(ptr != this.primes.head){
	    if(this.kModM(1,ptr.data.p).size != 1)
		return false;

	    ptr = ptr.next;
	}

	return true;
    }
    
}


var GLOBAL_v = 1.2;
var GLOBAL_d = "Jan 21, 2012";
var GLOBAL_n = null;

$(function(){
    //set the version number
    $("#version").html("<span id = \"vers\">Version " + GLOBAL_v + "</span><br>Last updated "+GLOBAL_d);
    $("#vers").click(function(){
	sendMessage("Changes","<h4>What's new in Version " + GLOBAL_v + "?</h4><ul><li>Display issues with long lists fixed.</li><li>Potentially long lines only displayed at users choice.</li><li>Added capability to input arithmetic expressions.</li></ul>");
    });

    //set the information about NoMSG
    $("#about")
	.button({icons: {primary: "ui-icon-info"}})
	.click(function(){
	    sendMessage("About NoMSG", "<h4>What is NoMSG?</h4><p>NoMSG is a proof generator. If you input a positive integer $n$, NoMSG will attempt to find a simple group of order $n$, or generate a proof that no such simple groups exist.</p><h4>How does it work?</h4><p>Magic.</p>");
	});


    //------------------------------

    $("#number_in").keyup(function(e){
	if(e.keyCode == 13)
	    $("#go").click();
    });

    $("#go")
	.button()
	.click(function() {
	    var v = $("#number_in").val();
	    for(var i = 0; i < v.length; ++i){
		var x = v[i].charCodeAt(0);
		if(x < 40 || x == 44 || x > 57){
			$("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>I don't think \"" + v + "\" is a number." + (x == 94? "This might be because I can't do exponentiation, and you used \"^.\" Sorry to disappoint.":" Please try again, with something slightly more \"numbery.\"") + "</div></div>");
		    return;
		}
	    }

	    try{
		var x = eval(v);

	    }
	    catch(e){
		$("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>Your input was invalid. I'm not exactly sure why, but you probably messed something up. Try again without messing up this time.</div></div>");
		return;
	    }

	    var y = Math.floor(x);

	    if(y != x || x < 1){
		$("#inner_statement").html("<p>There are no (simple) groups of order $" + x + "$.</p>");

		$("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>Your input was not a positive integer. Please try again, with number that has a more \"positive integer\" vibe to it.</div></div>");

		MathJax.Hub.Typeset();

		return;
	    }


	    GLOBAL_n = new Num(x);

	    GLOBAL_n.prove();
	    $("#proof").html(GLOBAL_n.showProof());
	    MathJax.Hub.Typeset();

	    //set expanding ability
	    $("span.list").click(function(){
		var b = parseInt(this.id.split(":")[0]);
		var x = this.id.split(":")[1].split("_")[0];
		var p = parseInt(this.id.split("_")[1]);

		//find the right prime
		var ptr = GLOBAL_n.primes.head.next;
		while(ptr != GLOBAL_n.primes.head){
		    if(ptr.data.p == p)
			break;
		    ptr = ptr.next;
		}

		console.log(p);

		if(x == "n")
		    $(this).html("$$" + inOrIs("n_{" + ptr.data.p + "}", ptr.data.np, (b == 0)).s + "$$");

		else if(x == "f"){
		    var ind = new Num(p);
		    ind.computeFactorList();
		    var s = toEnglishCentered(ind.factors, (b == 0));
		    $(this).html(s.split(">")[1].split("<")[0]);
		}

		this.id = "" + (1 - b) + ":"+this.id.split(":")[1];
		MathJax.Hub.Typeset();
	    });

	});

/*    var x = 5;
    var counter = 0;
    while(x <= 500000){
	x+=6
	GLOBAL_n = new Num(x);
	GLOBAL_n.prove();
	if(!GLOBAL_n.proofComplete){
	    console.log(GLOBAL_n.n);
	    counter++;
	}
    }

    console.log("-------");
    console.log(counter);*/

});

function setDialog(title){
    $("#message").dialog({
	width: 400,
	height: 230,
	resizable: false,
	autoOpen: false,
	modal: true,
	open: function(){
            $('.ui-widget-overlay').hide().fadeIn();
	},
	hide: "fade",
	title: title
    });

}

function sendMessage(title, message){
    $("#message").html(message);
    setDialog(title);
    $("#message").dialog("open");
    MathJax.Hub.Typeset();
}

