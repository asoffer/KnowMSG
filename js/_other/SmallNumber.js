MyNum.MAX = new BigNumber(9007199254740992);
MyNum.MAX_NUM = Math.pow(2,53);

function MyNum(n){
    this.big = false;
    this.temp = 0;

    var v = new BigNumber(n, 0);

    if(v.compare(MyNum.MAX) > 0){
	this.n = v;
	this.big = true;
    }
    else if(n instanceof BigNumber)
	this.n = toNumber(n);
    else
	this.n = n;
}


MyNum.prototype = {
    toString: function(){
	return this.n.toString();
    },

    add: function(m){

	this.temp = this.test(m);

	if(this.temp == 1)
	    return new MyNum(this.n.add(m.n));

	if(this.temp == 2)
	    return new MyNum(m.n.add(this.n));

	return new MyNum((this.n + m.n));
    },

    subtract: function(m){
	this.temp = this.test(m);

	if(this.temp == 1)
	    return new MyNum(this.n.subtract(m.n));

	if(this.temp == 2)
	    return new MyNum((new BigNumber(this.n)).subtract(m.n));

	return new MyNum(this.n - m.n);
    },

    multiply: function(m){
	this.temp = this.test(m);

	if(this.temp == 1)
	    return new MyNum(this.n.multiply(m.n));

	if(this.temp == 2)
	    return new MyNum(m.n.multiply(this.n));

	return new MyNum(this.n * m.n);
    },

    divide: function(m){
	this.temp = this.test(m);

	if(this.temp == 1)
	    return new MyNum(this.n.divide(m.n));

	if(this.temp == 2)
	    return new MyNum((new BigNumber(this.n)).divide(m.n));

	return new MyNum(this.n / m.n);
    },

    pow: function(m){
	this.temp = this.test(m);

	if(this.temp == 1)
	    return new MyNum(this.n.pow(m.n));

	return new MyNum((new BigNumber(this.n)).pow(m.n));
    },

    mod: function(m){
	this.temp = this.test(m);
	if(this.temp == 1)
	    return new MyNum(this.n.mod(m));
	if(this.temp == 2)
	    return this;

	return new MyNum(this.n % m.n);
    },

    compare: function(m){
	if(m instanceof Number)
	    this.n.compare(new MyNum(n));
	this.temp = this.test(m);
	if(this.temp == 1)
	    return this.n.compare(m.n);
	if(this.temp == 2)
	    return 1;

	if(this.n > m.n)
	    return 1;
	if(this.n == m.n)
	    return 0;
	return -1;

    },

    test: function(m){
	if(this.big)
	    return 1;
	if(m.big)
	    return 2;
	return 3;

	return this.big || (m instanceof BigNumber) || (m instanceof Number && m >= MyNum.MAX_NUM);
    },

    floor: function(){
	if(this.big)
	    return new MyNum(this.n);
	
	return new MyNum(Math.floor(this.n));
    }

}

//takes a bignumber that doesn't need to be in that format and
//converts it to a standard number
function toNumber(n){
    var c = 0;
    for(var i = 0; i < n._d.length; ++i){
	c *= 10;
	c += n._d[i];
    }


    return c;
}