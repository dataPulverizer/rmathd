module signrank;

import common;
import normal;
import gamma;
import core.memory.GC: free;

/*
** dmd signrank.d common.d normal.d gamma.d && ./signrank
*/

static double *w;
static int allocated_n;

static void w_free()
{
    if (!w) return;

    free(cast(void*) w);
    w = 0;
    allocated_n = 0;
}


void signrank_free()
{
    w_free();
}


static void w_init_maybe(int n)
{
    int u, c;

    u = n * (n + 1) / 2;
    c = (u / 2);

    if (w) {
        if(n != allocated_n) {
	    w_free();
	}
	else return;
    }

    if(!w) {
	w = (double *) calloc((size_t) c + 1, sizeof(double));
    
	if (!w){
		//MATHLIB_ERROR("%s", _("signrank allocation error"));
		doNothing();
	}
    
	allocated_n = n;
    }
}




