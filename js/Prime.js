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

    incompleteNPSize: function(){
	var c = 0;
	var ptr = this.np.head.next;
	while(ptr != this.np.head){
	    if(!ptr.data.proofComplete)
		++c;
	    ptr = ptr.next;
	}

	return c;
    },

    smallestNP: function(){
	var ptr = this.np.head.next;
	while(ptr != this.np.head){
	    if(!ptr.data.proofComplete)
		break;
	    ptr = ptr.next;
	}

	//what to do if they're all complete?
	return ptr.data;
    },

    prove: function(){
	var ptr = this.np.head.next;

	var flag = false;
	while(ptr != this.np.head){
	    var b = ptr.data.countTest();
	    flag = flag || b;
	    b = TechElementSize.apply(this.n, this, ptr.data);
	    flag = flag || b;
	    b = ptr.data.doubleNormalizerTest();
	    flag = flag || b;
	    b = ptr.data.symmetricDivisorTest();
	    flag = flag || b;
	    b = ptr.data.largeIntersectionAbelianTest();
	    flag = flag || b;
	    b = TechLI.apply(this.n, this, ptr.data);
	    flag = flag || b;
	    b = TechDP.apply(this.n, this, ptr.data);
	    flag = flag || b;

	    ptr = ptr.next;
	}
	
	//Since  we're deleting things later in the game, it's best to just check each time by iterating over this.np;
	ptr = this.np.head.next;
	while(ptr != this.np.head){
	    if(!ptr.data.proofComplete)
		return flag;

	    ptr = ptr.next;
	}

	this.proofComplete = true;
	return false;
    },

    showProof: function(){
	var pf = "";

	/*
	//okay, for now, just dump everything and don't even worry about the order
	var ptr = this.np.head.next;
	while(ptr != this.np.head){
	pf += "<h6>Case $n_{" + this.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

	ptr = ptr.next;
	}

	return pf;
	}
	};
	/*/

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
};
