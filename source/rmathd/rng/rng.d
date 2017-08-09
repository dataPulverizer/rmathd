/*
** This is a standalone module and exists independently of the original Rmath module.
** As so it is being released under the Boost Software License 1.0.
** Author: Chibisi Chima-Okereke
** Date: 2017-08-08
**
*/

module rmathd.rng.rng;

import std.random;

static bool seedSet = false;
static bool userSeed = false;
static uint randomSeed = 0;

void set_seed(uint _seed)
{
	randomSeed = _seed;
	userSeed = true;
	seedSet = false;
}

void seed_set()
{
	seedSet = true;
}

void get_seed(ref uint _seed)
{
	_seed = randomSeed;
}

class RandomNumberGenerator{
	immutable(string) RNGName;
	this()
	{
		RNGName = "default";
	}
	this(immutable(string) name)
	{
		RNGName = name;
	}
}
class MT19937: RandomNumberGenerator
{
	immutable(string) RNGName;
	Mt19937 engine;
	this(){
		super("MT19937");
		RNGName = "MT19937";
	}
	this(immutable(string) name){
		super("MT19937");
		RNGName = "MT19937";
	}
}
class MT1993764: RandomNumberGenerator
{
	immutable(string) RNGName;
	Mt19937_64 engine;
	this(){
		super("MT1993764");
		RNGName = "MT1993764";
	}
	this(immutable(string) name){
		super("MT1993764");
		RNGName = "MT1993764";
	}
}
class MINSTDRAND: RandomNumberGenerator
{
	immutable(string) RNGName;
	MinstdRand engine;
	this(){
		super("MINSTDRAND");
		RNGName = "MINSTDRAND";
	}
	this(immutable(string) name){
		super("MINSTDRAND");
		RNGName = "MINSTDRAND";
	}
}
class MINSTDRAND0: RandomNumberGenerator
{
	immutable(string) RNGName;
	MinstdRand0 engine;
	this(){
		super("MINSTDRAND0");
		RNGName = "MINSTDRAND0";
	}
	this(immutable(string) name){
		super("MINSTDRAND0");
		RNGName = "MINSTDRAND0";
	}
}

__gshared static RandomNumberGenerator threadRNG = new MT1993764();

void setRNG(RNG: RandomNumberGenerator)(RNG rng)
{
	threadRNG = rng;
}

immutable(string) gen_rand_num_code()
{
	return `if(!seedSet && userSeed){
		Rng.engine.seed(randomSeed);
		seed_set();
	}else if(!seedSet && !userSeed){
		Rng.engine.seed(unpredictableSeed);
		seed_set();
	}
	auto output = uniform!("[]", T, T)(lower, upper, Rng.engine);
	    return output;`;
}

auto rand(T = double)(T lower, T upper)
{
	if(threadRNG.RNGName == "MT19937"){
	    MT19937 Rng = cast(MT19937)threadRNG;
	    mixin (gen_rand_num_code());
	}
	else if(threadRNG.RNGName == "MT1993764"){
		MT1993764 Rng = cast(MT1993764)threadRNG;
		mixin (gen_rand_num_code());
	}
	else if(threadRNG.RNGName == "MINSTDRAND"){
		MINSTDRAND Rng = cast(MINSTDRAND)threadRNG;
		mixin (gen_rand_num_code());
	}
	else if(threadRNG.RNGName == "MINSTDRAND0"){
		MINSTDRAND0 Rng = cast(MINSTDRAND0)threadRNG;
		mixin (gen_rand_num_code());
	}
	else{
		MT1993764 Rng = cast(MT1993764)threadRNG;
		mixin (gen_rand_num_code());
	}
}
