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
    }
}
