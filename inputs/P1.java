
//class P1 {
//	public static void main(String[] args) {
//		try {
//			 A x;
//			 A y;
//			 A z;
//			 
//			 x = new A();
//			 y = new A();
//			 
//			 x.foo();
//			 
//			 synchronized(y) {
//				 z = new A();
//				 x.f = z;
//				 
//				 x.start();
//				 x.join();
//				 
//				 x.foo();
//				} 
//			}catch (Exception e) {
//					
//			} 
//	}
//}
//	 
//	class A extends Thread{
//		A f;
//		static A f5;
//		
//		public void run() {
//			try {
//				A a;
//				A b;
//				a = this;
//				synchronized(a) {
//					b = new A();
//					a.f = b;
//					this.f = b;
//				}
//			}catch(Exception e) {
//				
//			}
//		}
//		
//		public void foo()
//		{
//			try {
//				A p;
//				p = new A();
//				this.f = p;
//				
//				synchronized(p)
//				{
//					
//				}
//			}catch(Exception e)
//			{
//				
//			}
//		}
//	}

//class A
//{
//	A f;
//	
//	public void foo()
//	{
//		f = new A();
//	}
//}

//class A extends Thread
//{
//	A f;
//	static A f3;
//	
//	public void run()
//	{
//		try {
//			A p;
//			p = this;
//			
//			while(true)
//			{
//				synchronized(p)
//				{
//					A q;
//					f3 = p;
//					q = f3;
//				}
//			}
//					
//			
//		}
//		catch(Exception e)
//		{
//			
//		}
//	}
//	
//	public void foo()
//	{
//		f = new A();
//	}
//}

class P1 {
    public static void main(String[] args) {
    	A x, y, z, a, b, c, d, e;
    	
    	x = new A(); // O1 created, does not escape
    	y = new A(); // O2 created, deos not escape
    	z = new A(); // O3 created, deos not escape
    	a = new A(); // O4 created, deos not escape
    	b = new A(); // O5 created, deos not escape
    	c = new A(); // O6 created, deos not escape
    	d = new A(); // O7 created, deos not escape
    	e = new A(); // O8 created, deos not escape
    	
    	c.left = d;
    	c.right = e;
    	
    	a.left = b;
    	a.right = c;
    	
    	z.left = a;
    	y.right = z;
    	
    	x.sf = y; // all objects reachable from rho(y) escape -> O2, O3, ... O8 escape
    	
    	try {
    		synchronized(x) { // Since rho(x) does not has an escaping object, the synchronized construct can be removed
    			x.foo();
    		}
    	} catch (Exception exc) {}
    }	
}

class A {
    static A sf;
    A left;
    A right;
    
    void foo() {
    	System.out.println("Hello");
    }
}