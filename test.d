import std.stdio: writeln;
import std.math: fmax, fmin;

extern(C){
	int nearbyint();
}

mixin template test(alias X)
{
	double y = 3.14*X^^2.0;
}

template tmp(alias x)
{
	enum tmp = x.stringof ~ ` = ` ~ x.stringof ~ `^^2;`;
}

bool null_test(int* x)
{
	return x == null ? 1 : 0;
}

static auto addSq(T)(T x, T y)
{
	return 2.0*(x*x + y*y);
}

void main()
{
	mixin test!(4.);
	writeln(y);
	void alter()
	{
		y = 8.;
	}
	alter();
	writeln(y);
	writeln("double(0): ", double(0));
	double tp = 2.2;
	mixin (tmp!tp);
	writeln("tp: ", tp);
	//tp = 5.5;
	mixin (tmp!tp);
	writeln("tp: ", tp);

	writeln("fmax: ", fmax(double.nan, 2.));
	writeln("fmin: ", fmin(double.nan, 1.5));
	int* y;
	int z = 180;
	//y = &z; //null
	writeln("Null test: ", null_test(y));
	writeln(nearbyint());
	writeln("static auto function test: ", addSq(4, 5));
	import std.format: format;
	writeln(format("Test: %.19f", 0x1.fffffffffffffp-1));
}

