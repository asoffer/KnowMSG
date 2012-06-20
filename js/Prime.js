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
            var b = ptr.data.proofComplete;
            TechCount.apply(this.n, this, ptr.data);
            TechDNorm.apply(this.n, this, ptr.data);
            TechSymDiv.apply(this.n, this, ptr.data);
            TechNormInSym.apply(this.n, this, ptr.data);
            TechLAI.apply(this.n, this, ptr.data);
            TechLI.apply(this.n, this, ptr.data);
            TechDP.apply(this.n, this, ptr.data);
            TechNC2.apply(this.n, this, ptr.data);
            TechNC.apply(this.n, this, ptr.data);

            flag = flag || (b!=ptr.data.proofComplete);

            ptr = ptr.next;
        }

        ptr = this.np.head.next;
        while(ptr != this.np.head){
            if(!ptr.data.proofComplete)
                return flag;

            ptr = ptr.next;
        }

        this.proofComplete = true;
        return false;
    }
};
