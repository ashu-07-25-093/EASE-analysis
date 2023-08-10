# a26235
## Instructions for Assignment 2:

Escape Analysis is given below.

http://www.cse.iitm.ac.in/~krishna/cs6235/a2.html

You need to implement the *internalTransform* method in *EscapeAnalysis* class under *submit_a2* package.

 *A2* is the main class. It takes the input file from *inputs* folder and queries file from *queries* folder.
 
 ###### Running from command-line:
 
 From the project folder (a26235) run the following command in command-line.
 
 java -classpath "bin/:lib/soot-4.3.0-jar-with-dependencies.jar:" -Dtest.file="queries/Q1.txt" submit_a2.A2 -pp -cp "inputs" -w -app -p cg.cha enabled:true	-p cg.spark enabled:false P1
 
 *Note* : You can set the classpath appropriately if you have different file structure. Remember to add path of soot jar to the classpath while running from command line.
 
- The queries file path is given by -Dtest.file, which can be accessed using System.getProperty("test.file")
- **-pp** : indicates to prepend java class path to soot classpath. Initially soot classpath is empty
- **-cp "inputs"** : indicates to include "inputs"(where P1.java is placed) in soot classpath 
- **-w** : indicates to run in whole program mode.
- **-app** : indicates to run in application mode. Whatever classes referred from argument classes (here P1) will also be application classes(except library classes). Application classes are the ones that will be processed by soot.
- **-p cg.cha enabled:true** : enables call graph by CHA.
- **-p cg.spark enabled:false** : disables Spark call graph 

All these options are encoded in the getOptions method of A2 class.

If you want to give any further options or change the existing options, you can try them by passing command line arguments. For normal functioning required for assignment, you need not change any options. 
 
 
      
###### Query form      

Each query is of the form
*&lt;class&gt;:&lt;method&gt;*
      
It represents, "Can the synchronization construct be removed in class *&lt;class&gt;*, method *&lt;method&gt;*? "
      
Your analysis should answer either "yes" or "No" for this.

The answers should follow the same order as of queries in the query file.
      
Your answers should be present in static String array *answers* in *A2* class which can be accessed as *A2.answers*.

###### Example

Consider the below example,
      
```

class P1 {
	public static void main(String[] args) {
		try {
			 A x;
			 A y;
			 A z;
			 
			 x = new A();
			 y = new A();
			 synchronized(y) {
				 z = new A();
				 x.f = z;
				 x.start();
				 x.join();
				} 
			}catch (InterruptedException e) {
					
			} 
	}
}
	class A extends Thread{
		A f;
		
		public void run() {
			try {
				A a;
				A b;
				a = this;
				synchronized(a) {
					b = new A();
					a.f = b;
				}
			}catch(Exception e) {
				
			}
		}
	}
	

```
      
The Queries
      
```
P1:main
A:run
```

should answer
```      
No
No
```
It means, A1.answers[0] should contain Yes, A1.answers[1] should contain No, and so on..
