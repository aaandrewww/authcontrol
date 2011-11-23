#include <stdio.h>
#include <proof.h>
#include <formula.h>

int main() 
{
	test();
	return 0;
} 

void test(){
	struct principal prin;
	prin.prin.pcpl = "A\0";
	prin.type = PCPL;

	Pred_f pred;
	pred.principal = &prin;
	pred.pred = "OK\0";

	struct formula f;
	f.type = PRED;
	f.form.pred_f = pred;
	formula_print(&f);
}
	
