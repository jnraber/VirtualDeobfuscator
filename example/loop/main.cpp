
#include <stdio.h>

int foo(int range1, int range2)
{
	static bool only = true;
	int sum = 0;
	int sum2 = 0;

	for (int i = 0; i < range1; i++)
	{
		sum += i;
		for (int z = 0; z < range2; z++)
			if (i == 2 && z == 1)
			{
				if (only)
				{
					_asm { mov eax, 0xDEADBEEF } 
					only = false;
				}
			}
			sum2 += sum + 1;
	}

	return sum2;
}

int main(int argc, char **argv)
{
	int sum = 0;

	sum = foo(4, 2);
	printf("sum is %d \n", sum);

	sum = foo(3, 2);
	printf("sum is %d \n", sum);


	printf("Done\n");
	
	return 0;
}