package submit_a2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.common.collect.Sets;

import dont_submit.EscapeQuery;
import soot.ArrayType;
import soot.Body;
import soot.BodyTransformer;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.EnterMonitorStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.toolkits.callgraph.CHATransformer;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.Targets;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.Chain;

public class EscapeAnalysis extends SceneTransformer{

	class DS
	{
		// roh-map obj-references
		Map<String, Set<String>> ro = new HashMap<>();
		
		// sigma-map, obj- fields- reference
		Map<String, Map<String, Set<String>>> sigma = new HashMap<>();
		
		// escape map
		Set<String> escapeMap = new HashSet<>();
	}
	class OUT
	{
		// sigma-map, obj- fields- reference
		Map<String, Map<String, Set<String>>> sigma = new HashMap<>();
		
		// escape map
		Set<String> escapeMap = new HashSet<>();
		
		// return value, obj-reference
		Map<String, Set<String>> retVal = new HashMap<>();
		
	}
	
	class Synch
	{
		Set<String> ref = new HashSet<>();
		Set<String> emap = new HashSet<>();
	}
	
	static int cnt = 1;
	Map<Unit, DS> unitIn = new HashMap<>();
	Map<SootMethod, DS> InSummary = new HashMap<>();
	Map<SootMethod, OUT> OutSummary = new HashMap<>();
	List<SootMethod> interWorklist;
	
	List<SootClass> threadSubClasses;
	Chain<SootClass> allClasses;
	List<SootMethod> allMethods;
	List<SootField> insfield_escape = new ArrayList<SootField>();
	
	Map<String, Map<String, Synch>> synch = new HashMap<>();
	
	Map<Stmt, String> visited = new HashMap<>();
	
	// This function is calculating all the fields of a class, and it's superclass recursively,
	// and then returns all those soot fields.
	synchronized List<SootField> getAllFields(Value val)
	{	
		// convert into refType
		
		List<SootField> sf = new ArrayList<>();
		
		if(val.getType() instanceof RefLikeType && !(val.getType() instanceof ArrayType))
		{
			RefType rf = (RefType) val.getType();
			
			Chain<SootField> fields = null;
			
			// find the sootclass and then it's fields
			fields = rf.getSootClass().getFields();
			
			for(SootField s:fields)
				sf.add(s);
			
			SootClass c = rf.getSootClass();
			
			// adding all the fields of superclass
			while(c.hasSuperclass())
			{
				// getting superclass of current sootClass
				c = c.getSuperclass();
				
				Chain<SootField> fs = c.getFields();
				
				if(!fs.isEmpty())
				{
					for(SootField f:fs)
					{
						if(!sf.contains(f))
							sf.add(f);
					}
				}
			}
			
		}
		
		return sf;
		
	}
	
	// This function is used to calculate the concept of reachable heap....
	// When we're making the field of any var to bottom, we have to first calculate all the other
	// reachable reference from this var and make their fields also bottom
	synchronized Set<String> getReachableRefs(Set<String> st, Map<String, Set<String>> in_old_ro, Map<String, Map<String, Set<String>>> in_old_sigma)
	{
		// taking temporary ro and sigma map
		Map<String, Set<String>> in_new_ro = new HashMap<>();
		Map<String, Map<String, Set<String>>> in_new_sigma = new HashMap<>();
		
		Set<String> set = new HashSet<>();
		set = st;
		
		in_new_ro.putAll(in_old_ro);
		in_new_sigma.putAll(in_old_sigma);
		
		ArrayList<String> reachable_fields = new ArrayList<>();
		Set<String> final_fields = new HashSet<>();
		
		// adding all the refs of current variable
		
		if(st!=null)
		{
			reachable_fields.addAll(set);
			
			// to store the final fields for which we will make them to bottom
			
			
			// visited map, to store for which refs, we've already calculated, otherwise loop will go into infinite
			Map<String, Boolean> visited = new HashMap<>();
			
			while(!reachable_fields.isEmpty())
			{
				// removing first element from the arrayList
				String str = reachable_fields.remove(0);
				
				// if not visited already then only calculate
				if(!visited.containsKey(str))
				{
					// adding ref to final field
					final_fields.add(str);
					
					Map<String, Set<String>> mp = new HashMap<>();
					
					if(in_new_sigma.containsKey(str))
						mp = in_new_sigma.get(str);
					
					// for all the fields of curr ref, iterate through map and add the refs, this field point to...
					for(Map.Entry<String, Set<String>> entry:mp.entrySet())
					{
						Set<String> sett = new HashSet<>();
						sett = entry.getValue();
						
						reachable_fields.addAll(sett);
					}
					
					visited.put(str, true);
				}
			}
		}
		
		return final_fields;
		
	}
	
	Map<String, Set<String>> roUnion(Map<String, Set<String>> ro1, Map<String, Set<String>> ro2)
	{
		for(Map.Entry<String, Set<String>> entry:ro2.entrySet())
		{
			String key = entry.getKey();
			
			// if current key is already contained, then do union
			if(ro1.containsKey(key))
			{
				Set<String> s1 = new HashSet<>(ro1.get(key));
				
				Set<String> s2 = new HashSet<>(ro2.get(key));
				
				Set<String> s3 = new HashSet<>();
				s3 = Sets.union(s1, s2);
				
				ro1.put(key, s3);
			}
			// if new key, then simply put it to the map...
			else
			{
				Set<String> s1 = new HashSet<>(ro2.get(key));
				
				ro1.put(key, s1);
			}
		}
		
		return ro1;
	}
	
	Map<String, Map<String, Set<String>>> sigmaUnion(Map<String, Map<String, Set<String>>> sigma1, Map<String, Map<String, Set<String>>> sigma2)
	{
		// to calculate the union of out_sigma of all predecessors 
		for(Map.Entry<String, Map<String, Set<String>>> entry:sigma2.entrySet())
		{
			String key = entry.getKey();    // reference
			
			// if already contains the ref
			if(sigma1.containsKey(key))
			{
				// get the map for current ref from both the sigma maps
				Map<String, Set<String>> mp = new HashMap<>(sigma2.get(key));
				
				Map<String, Set<String>> mp2 = new HashMap<>(sigma1.get(key));
				
				// both sigma maps contains the same fields, to iterate through map and do union of the refs, pointed by
				// field
				for(Map.Entry<String, Set<String>> ent:mp.entrySet())
				{
					String k = ent.getKey();   // field
					
					Set<String> s1 = new HashSet<>();  // set of refs pointed by field
					if(mp.containsKey(k))
						s1 = mp.get(k);
					
					Set<String> s2 = new HashSet<>();
					if(mp2.containsKey(k))
						s2 = mp2.get(k);
					
					Set<String> s3 = new HashSet<>();
					s3 = Sets.union(s1, s2);     // union of both the sets
					
					mp2.put(k, s3);
				}
				sigma1.put(key, mp2);
			}
			// if not present, then simply put it to map
			else
			{
				Map<String, Set<String>> mp = new HashMap<>(sigma2.get(key));
				
				sigma1.put(key, mp);
			}	
		}
		
		return sigma1;
	}
	
	boolean compareMap(Map<String, Map<String, Set<String>>> map1, Map<String, Map<String, Set<String>>> map2)
	{
		boolean flag = true;
		
		if(!map1.keySet().equals(map2.keySet()))
			flag = false;
		
		else
		{
			for(Map.Entry<String, Map<String, Set<String>>> entry: map1.entrySet())
			{
				String key = entry.getKey();
				
				Map<String, Set<String>> mp1 = map1.get(key);
				Map<String, Set<String>> mp2 = map2.get(key);
				
				if(!mp1.keySet().equals(mp2.keySet()))
				{
					flag = false;
					break;
				}
				else
				{
					for(Map.Entry<String, Set<String>> ent:mp1.entrySet())
					{
						String k = ent.getKey();
						
						Set<String> set1 = new HashSet<>(mp1.get(k));
						Set<String> set2 = new HashSet<>(mp2.get(k));
						
						if(!set1.equals(set2))
						{
							flag = false;
							break;
						}
					}
					if(!flag)
						break;
				}
			}
		}
		
		return flag;
	}
	
	DS weakUpdate(DS ds_, String lhs, String rhs, String field)
	{
		DS d = new DS();
		d.ro = ds_.ro;
		d.sigma = ds_.sigma;
		d.escapeMap = ds_.escapeMap;
		
		// weak update
		if(!d.ro.isEmpty())
		{
			if(d.ro.containsKey(lhs))
			{
			
				// getting all the refs, base is pointing to...
				Set<String> st2 = new HashSet<>();
				st2 = d.ro.get(lhs);
				
				// to check if lhs base is not pointing to any escape object
				boolean flag3 = false;
				
				for(String str_:st2)
				{
					if(d.escapeMap.contains(str_))
					{
						flag3 = true;
						break;
					}
				}
				
				if(!st2.contains("Og") && !flag3)
				{
					// getting all the refs, rhs is pointing to...
					Set<String> set_rhs = new HashSet<>();
					
					if(d.ro.containsKey(rhs.toString()))
						set_rhs = new HashSet<>(d.ro.get(rhs.toString()));
					
					// for each of the ref pointed by base, first get all the old refs of the given field,
					// then do union of old refs with new refs(refs pointed by rhs), and put it back in the map...
					for(String s:st2)
					{
						Set<String> s1 = new HashSet<>();
						boolean flag1 = false;
						
						if(d.sigma.containsKey(s) && d.sigma.get(s).containsKey(field))
						{
							s1 = new HashSet<>(d.sigma.get(s).get(field));
							flag1 = true;
						}
						
						s1 = Sets.union(s1, set_rhs);
						
						// doing union of old and new refs
						
						if(flag1)
							d.sigma.get(s).put(field, s1);

					}
				}
				
			}	
		}
		
		return d;
	}
	
	// implementation of flowFunction, which will take unit, it's ro and sigma map, bottom and visited map as an arguments
	synchronized void flowFunction(Unit u, DS predInDS, CallGraph cg, UnitGraph cfg, String currClass_str, String currMethod_str)
	{
		// new ro and sigma map, on which we will do calculations and return
		Map<String, Set<String>> in_new_ro = new HashMap<>();
		
		Map<String, Map<String, Set<String>>> in_new_sigma = new HashMap<>();
		
		Set<String> in_new_escape = new HashSet<>();
		
		// doing deep copy of ro and sigma map to new ro and sigma map
		for(Map.Entry<String, Set<String>> entry: predInDS.ro.entrySet())
		{
			String key = entry.getKey();
			
			in_new_ro.put(key, new HashSet<String>(predInDS.ro.get(key)));
		}
		
		for(Map.Entry<String, Map<String, Set<String>>> entry: predInDS.sigma.entrySet())
		{
			String key = entry.getKey();
			
			in_new_sigma.put(key, new HashMap<String, Set<String>>());
			
			Map<String, Set<String>> mp1 = predInDS.sigma.get(key);
			
			for(Map.Entry<String, Set<String>> ent:mp1.entrySet())
			{
				String k = ent.getKey();
				
				in_new_sigma.get(key).put(k, new HashSet<String>(mp1.get(k)));
			}
		}
		
		for(String e:predInDS.escapeMap)
			in_new_escape.add(e);
		
		Set<String> mname = new HashSet<>();
		mname.add("start");
		mname.add("join");
		mname.add("wait");
		mname.add("notify");
		mname.add("notifyAll");
		mname.add("sleep");
		
		// converting unit to statement
		Stmt stmt = (Stmt) u;
		
		if(stmt instanceof InvokeStmt)
		{	
			InvokeExpr ie = stmt.getInvokeExpr();
			
			Value v = ((InstanceInvokeExpr) ie).getBase();
			
			SootMethod callerMethod = ((InstanceInvokeExpr) ie).getMethod();
			
			Iterator<Edge> outEdges = cg.edgesOutOf(u);
						
			Local this_;
			
			while(outEdges.hasNext())
			{
				Edge e = outEdges.next();
				SootMethod targetMethod = e.getTgt().method();
				
				if(!targetMethod.isConstructor() && !mname.contains(targetMethod.getName()))
				{
					if(OutSummary.containsKey(targetMethod))
					{
						in_new_sigma = sigmaUnion(in_new_sigma, OutSummary.get(targetMethod).sigma);
						
						in_new_escape = Sets.union(in_new_escape, OutSummary.get(targetMethod).escapeMap);
					}
						
				}
			}
			
			outEdges = cg.edgesOutOf(u);
			while(outEdges.hasNext())
			{
				Edge e = outEdges.next();
				
				SootMethod targetMethod = e.getTgt().method();
				
				
				if(!targetMethod.isConstructor() && !mname.contains(targetMethod.getName()) && !targetMethod.toString().contains("java.") && !targetMethod.toString().contains("jdk."))
				{
					// insummary of target method
					DS inSummary = InSummary.get(targetMethod);
					//DS unitSummary = unitIn.get(u);
					
					this_ = targetMethod.getActiveBody().getThisLocal();
					
					String thisstr = this_.toString();
					
					// getting ro from insummary of targetMethod
					Map<String, Set<String>> ro_method = inSummary.ro;
					// for refs pointed by thisParam
					
					
					if(!ro_method.containsKey(thisstr))
					{
						ro_method.put("this", new HashSet<>());
					}
										
					Set<String> set_method = new HashSet<>(ro_method.get("this"));
					
					//getting ro from unitSummary
					Map<String, Set<String>> ro_unit = in_new_ro;
					// for refs pointed by base of invokeExpr
					Set<String> set_unit = new HashSet<>();
					
					if(ro_unit.containsKey(v.toString()))
						set_unit = ro_unit.get(v.toString());
					
					Set<String> em_method = inSummary.escapeMap;
					Set<String> em_unit = in_new_escape;
					
					Map<String, Map<String, Set<String>>> sigma_unit = in_new_sigma;
					Map<String, Map<String, Set<String>>> sigma_method = inSummary.sigma;
					
					boolean flag = compareMap(sigma_unit, sigma_method);
					
					if(!set_unit.equals(set_method) || !em_unit.equals(em_method) || !flag)
					{	
						interWorklist.add(targetMethod);
						
						ro_method.put("this", Sets.union(set_method, set_unit));
						
						sigma_method = sigmaUnion(sigma_method, sigma_unit);
						
						em_method = Sets.union(em_method, em_unit);
						
						inSummary.ro = ro_method;
						inSummary.sigma = sigma_method;
						inSummary.escapeMap = em_method;
												
						InSummary.put(targetMethod, inSummary);
					}
				}
				
			}
			
		}
		// checking if the stmt is of type definition
		else if(stmt instanceof DefinitionStmt)
		{
			DefinitionStmt ds = (DefinitionStmt) stmt;
			
			// getting the left and right operands of DefinitionStmt
			Value lhs = ds.getLeftOp();
			Value rhs = ds.getRightOp();
			
			// if the stmt is of type allocation
			if(rhs instanceof NewExpr)
			{
				// getting the lhs variable
				String local = lhs.toString();
				Set<String> st = new HashSet<>();
				
				String s = "";
				
				// if this stmt is not visited then only assign new ref to this stmt
				// in case of loop, we have perform new allocation only one time, that's why we use visited map
				if(!visited.containsKey(stmt))
				{
					s = "R"+cnt;      // creating new ref
					st.add(s);
					cnt++;
					
					visited.put(stmt, s);   // make curr stmt as visited
				}
				else
				{	
					// getting the stmt for which we've already done calculations
					s = visited.get(stmt); 
					st.add(s);
					// re-assigning the same ref to curr stmt
					in_new_ro.put(local, st);
				}
				
				in_new_ro.put(local, st);
				
				SootClass class_ = ((RefType)rhs.getType()).getSootClass();
				
				//System.out.println("in new..");
				if(threadSubClasses.contains(class_))
				{
					in_new_escape.add(s);
				}
				
				// calculations of sigma field, when allocation is being done,
				// fields for that ref will also get initialized to empty
				
				Map<String, Set<String>> field = new HashMap<>();
				
				// getting all the fields
				List<SootField> fields = getAllFields(lhs);
				
				// for each sootField, check if it's RefLikeType, then only add it to the map and initialize
				for(SootField f:fields)
				{
					if(f.getType() instanceof RefLikeType)
					{
						field.put(f.getName().toString(), new HashSet<>());
					}
				}
				
				in_new_sigma.put(s, field);
			}
			// if rhs is any invokeExpr
			else if(rhs instanceof InvokeExpr)
			{
				// getting lhs field
				String local = lhs.toString();
				
				Set<String> og = new HashSet<>();
				og.add("Og");
				
				in_new_ro.put(local, og);    // lhs assigned to bottom
				
				// calculation for arguments, we've to make the fields of arguments to bottom
				
				// getting the list containing the arguments passing to the function
				List<Value> val = ((InvokeExpr) rhs).getArgs();
				
				// check if function call contains any arguments, then only do calculations
				if(!val.isEmpty())
				{
					// for each of the argument, first get all the refs it's pointing to
					// then calculate all the reachable fields from these refs.
					// now get all the soot fields of current argument, and for each of the reachable field -> for each 
					// sootFields, assign bottom
					for(Value v:val)
					{
						Set<String> set = new HashSet<>();
						if(in_new_ro.containsKey(v.toString()))
							set = new HashSet<>(in_new_ro.get(v.toString()));
						
						// getting all the reachable fields of current argument
						Set<String> reachable_fields = getReachableRefs(set, in_new_ro, in_new_sigma);
						
						// getting all the sootfields of current argument
						
						List<SootField> arg_sootfields = getAllFields(v);
						
						// iterate through all the reachable fields
						for(String str:reachable_fields)
						{
							// iterate through all the sootFields
							for(SootField f:arg_sootfields)
							{
								// check it the current sootField it of RefLike Type, then only make it as bottom
								if(f.getType() instanceof RefLikeType)
								{
									if(in_new_sigma.containsKey(str))
										in_new_sigma.get(str).put(f.getName().toString(), og);
								}
							}
						}
					}
				}
				// 1.) z = foo(y), 2.) z = x.foo(y)
				// if rhs is of 2nd type then we have to get the base of the rhs and make all the fields bottom
				if(rhs instanceof InstanceInvokeExpr)
				{
					// getting the base
					Value v = ((InstanceInvokeExpr) rhs).getBase();
				
					// base fields manipulation
					Set<String> set = new HashSet<>();
					
					if(in_new_ro.containsKey(v.toString()))
						set = in_new_ro.get(v.toString());
					
					// getting all the reachable fields from the base
					Set<String> reachable_fields = getReachableRefs(set, in_new_ro, in_new_sigma);
					
					// getting all the sootFields of base
					List<SootField> arg_sootfields = getAllFields(v);
					
					// for each reachable field, iterate through all sootFields of base and assign bottom
					for(String str:reachable_fields)
					{
						for(SootField f:arg_sootfields)
						{
							// check if field is of RefLikeType
							if(f.getType() instanceof RefLikeType)
							{
								if(in_new_sigma.containsKey(str))
									in_new_sigma.get(str).put(f.getName().toString(), new HashSet<>(og));
							}
						}
					}
				}
				
			}
			
			
			// store statement x.f = y
			else if(lhs instanceof InstanceFieldRef && (rhs.getType() instanceof RefLikeType && !(rhs instanceof InstanceFieldRef)))
			{
				// getting the base and field from the lhs
				String local = ((InstanceFieldRef) lhs).getBase().toString();
				String field_str = ((InstanceFieldRef) lhs).getField().getName().toString();
				
				SootField field = ((InstanceFieldRef) lhs).getField();
				
				Set<String> st1 = new HashSet<>();
				
				if(in_new_ro.containsKey(rhs.toString()))
					st1 = in_new_ro.get(rhs.toString());
				
				if(field.isStatic())
				{
					// getting reachable fields
					Set<String> reachable_fields = getReachableRefs(st1, in_new_ro, in_new_sigma);
					
					for(String str:reachable_fields)
					{
						in_new_escape.add(str);
					}
				}
				
				else
				{
					Set<String> st = new HashSet<>();
					
					if(in_new_ro.containsKey(local))
						st = in_new_ro.get(local);
					
					// to check if left side is pointing to any escape object
					boolean flag = false;
					
					for(String s:st)
					{
						if(in_new_escape.contains(s))
						{
							flag = true;
							break;
						}
					}
					
					// if left side is pointing to any escape object then make all fields reachable from rhs as escape
					
					if(flag)    
					{
						Set<String> st2 = new HashSet<>();
						
						if(in_new_ro.containsKey(rhs.toString()))
							st2 = in_new_ro.get(rhs.toString());
						
						// getting reachable fields
						Set<String> reachable_fields = getReachableRefs(st2, in_new_ro, in_new_sigma);
						
						for(String str:reachable_fields)
						{
							in_new_escape.add(str);
						}
					}
					
					
					DS ds_ = new DS();
					
					ds_.ro = in_new_ro;
					ds_.sigma = in_new_sigma;
					ds_.escapeMap = in_new_escape;
					
					ds_ = weakUpdate(ds_, local, rhs.toString(), field_str);
					
					in_new_ro = ds_.ro;
					in_new_sigma = ds_.sigma;
					in_new_escape = ds_.escapeMap;
				}	
			}
			// load statement x = y.f
			else if(!(lhs instanceof InstanceFieldRef) && rhs instanceof InstanceFieldRef)
			{
				// getting the base and field of rhs
				String base = ((InstanceFieldRef) rhs).getBase().toString();
				String field = ((InstanceFieldRef) rhs).getField().getName().toString();
				
				// to store the refs pointed by base
				Set<String> st = new HashSet<>();
				
				if(in_new_ro.containsKey(base))
				{
					if(in_new_ro.get(base).contains("Og"))
					{
						st.add("Og");
						in_new_ro.put(lhs.toString(), st);
					}
					
					else
					{
						// getting the refs pointed by base
						if(in_new_ro.containsKey(base))
							st = in_new_ro.get(base);
						
						boolean flag = false;
						
						for(String s:st)
						{
							if(in_new_escape.contains(s))
							{
								flag = true;
								break;
							}
						}
						
						if(flag)
						{
							Set<String> st1 = new HashSet<>();
							st1.add("Og");
							in_new_ro.put(lhs.toString(), st1);
						}
						
						else
						{	
							// to store the union of the refs pointed by field, for all refs poitned by base
							Set<String> set_ = new HashSet<>();
							
							// for each refs pointed by base
							for(String s:st)
							{
								// get all the refs pointed by field of current ref
								Set<String> set = new HashSet<>();
								
								if(in_new_sigma.containsKey(s) && in_new_sigma.get(s).containsKey(field))
									set = in_new_sigma.get(s).get(field);
								
								// performing the union
								set_ = Sets.union(set_, set);
							}
							
							// assigning union set to the ro of lhs
							in_new_ro.put(lhs.toString(), set_);
						}
					}
				}
				
							
			}
			// copy statement x = y
			else if(lhs instanceof Local && rhs instanceof Local)
			{
				// to store the refs pointed by rhs
				Set<String> st = new HashSet<>();
				
				if(in_new_ro.containsKey(rhs.toString()))
					st = in_new_ro.get(rhs.toString()); 
				
				in_new_ro.put(lhs.toString(), st);
								
			}
			
			else if(ds.containsFieldRef())
			{	
				if(lhs instanceof StaticFieldRef)
				{	
					Set<String> st1 = new HashSet<>();
					
					if(in_new_ro.containsKey(rhs.toString()))
						st1 = in_new_ro.get(rhs.toString());
					
					// getting reachable fields
					Set<String> reachable_fields = getReachableRefs(st1, in_new_ro, in_new_sigma);
					
					for(String str:reachable_fields)
					{
						in_new_escape.add(str);
					}
				}
				
				else
				{	
					Set<String> st = new HashSet<>();
					st.add("Og");
					
					in_new_ro.put(lhs.toString(), st);
				}
				
				
			}
			
		}
		
		else if(stmt instanceof EnterMonitorStmt)
		{
			EnterMonitorStmt ems = (EnterMonitorStmt) stmt;
			
			Synch s = new Synch();
			
			s.ref = in_new_ro.get(ems.getOp().toString());
			
			s.emap = in_new_escape;
			
			Map<String, Synch> mp = new HashMap<>();
			mp.put(currMethod_str, s);
			
			synch.put(currClass_str, mp);
			
			Synch sy = synch.get(currClass_str).get(currMethod_str);
			
		}
				
		// creating dummy map to make similar structure as sigma map, to add it to the list...so that we can return
		// ro and sigma map
		
		predInDS.ro = new HashMap<>(in_new_ro);
		predInDS.sigma = new HashMap<>(in_new_sigma);
		predInDS.escapeMap = new HashSet<>(in_new_escape);
		
		unitIn.put(u, predInDS);
		
	}
	
	@Override
	synchronized protected void internalTransform(String phaseName, Map<String, String> options) {
		/*
		 * Implement your escape analysis here
		 */
		

		CallGraph cg = Scene.v().getCallGraph();		
		
		interWorklist = new ArrayList<SootMethod>();
		
		//SootMethod mainMethod = Scene.v().getMainMethod();
		interWorklist.add(Scene.v().getMainMethod());
		
		SootClass thread = Scene.v().getSootClass("java.lang.Thread");
		List<SootClass> classes = Scene.v().getActiveHierarchy().getSubclassesOf(thread);
		
		threadSubClasses = new ArrayList<SootClass>(classes);
		threadSubClasses.removeIf(c -> c.isLibraryClass());
		
		allClasses = Scene.v().getApplicationClasses();
		
		allMethods = new ArrayList<>();
		
		for(SootClass class_:allClasses)
		{
			for(SootMethod method:class_.getMethods())
			{
				if(!method.isConstructor())
				{
					//System.out.println("method adding : "+method);
					allMethods.add(method);
				}
			}
		}
		
		for(SootMethod method:allMethods)
		{
			InSummary.put(method, new DS());
			OutSummary.put(method, new OUT());
		}
		
		// creating escape_map for instance field for all classes
		
		for(SootClass sc:threadSubClasses)
		{
			Chain<SootField> fields = sc.getFields();
			
			for(SootField f:fields)
			{
				insfield_escape.add(f);
			}
		}			
		
		while(!interWorklist.isEmpty())
		{
			SootMethod currMethod = interWorklist.get(0);
			
			interWorklist.remove(0);
			
			Body body = currMethod.getActiveBody();
			
			String currClass_str = currMethod.getDeclaringClass().toString();
			String currMethod_str = currMethod.getName().toString();			
			
			Set<Unit> localWorklist = new HashSet<>();
			
			UnitGraph cfg = new BriefUnitGraph(body);
			
			OUT currMethodOut = OutSummary.get(currMethod);
			
			for(Unit u:body.getUnits())
			{
				localWorklist.add(u);
				
				unitIn.put(u, new DS());
				
				if(cfg.getPredsOf(u).isEmpty())
				{	
					DS d = InSummary.get(currMethod);
					
					DS d1 = new DS();
					d1.ro = new HashMap<>(d.ro);
					d1.sigma = new HashMap<>(d.sigma);
					d1.escapeMap = new HashSet<>(d.escapeMap);
					
					unitIn.put(u, d1);
				}
			}
			
			while(!localWorklist.isEmpty())
			{
				Unit currUnit = localWorklist.iterator().next();      // current unit
				
				localWorklist.remove(currUnit);
				
				List<Unit> preds = cfg.getPredsOf(currUnit);     // getting the predecessor of current unit
				
				DS currDS = unitIn.get(currUnit);
							
				// getting the in_ro and in_sigma of current unit
				Map<String, Set<String>> dfin_ro = new HashMap<>(currDS.ro);
				Map<String, Map<String, Set<String>>> dfin_sigma = new HashMap<>(currDS.sigma);
				Set<String> dfin_em = new HashSet<>(currDS.escapeMap);
				
				// to store the updated in_ro and in_sigma for current unit
				Map<String, Set<String>> toteff_ro = new HashMap<>();
				Map<String, Map<String, Set<String>>> toteff_sigma = new HashMap<>();
				Set<String> toteff_em = new HashSet<>();
				
				
				// visited map, to keep track of statement inside loop visited only once during loop...
				
				
				// looping over all predecessors of the current unit
				for(Unit pred:preds)
				{
					Stmt stm = (Stmt) pred;
					
					DS predDS = unitIn.get(pred);
					
					// calling the flowFuction
					flowFunction(pred, predDS, cg, cfg, currClass_str, currMethod_str);
					
					// store the out_ro of current predecessor
					Map<String, Set<String>> pred_out_ro = new HashMap<>(unitIn.get(pred).ro);
					// store the out_sigma of current predecessor
					Map<String, Map<String, Set<String>>> pred_out_sigma = new HashMap<>(unitIn.get(pred).sigma);
					
					Set<String> pred_out_em = new HashSet<>(unitIn.get(pred).escapeMap);
										
					toteff_ro = roUnion(toteff_ro, pred_out_ro);
					toteff_sigma = sigmaUnion(toteff_sigma, pred_out_sigma);
					toteff_em = Sets.union(toteff_em, pred_out_em);
					
				}
				
				// if(old in_ro != new in_ro || old in_sigma != new in_sigma) for current unit of worklist
				// then update and add all it's successors to worklist...
				if(!dfin_ro.equals(toteff_ro) || !dfin_sigma.equals(toteff_sigma) || !dfin_em.equals(toteff_em))
				{
					
					currDS.ro = roUnion(currDS.ro, toteff_ro);
					currDS.sigma = sigmaUnion(currDS.sigma, toteff_sigma);
					currDS.escapeMap = Sets.union(currDS.escapeMap, toteff_em);
					
					// union of currds and totalef put in currUnit
					unitIn.put(currUnit, currDS);
					
					List<Unit> successors = cfg.getSuccsOf(currUnit);      // getting the successors of current unit
					
					localWorklist.addAll(successors);      // adding successors to the worklist
				}				
			}
			
			Unit lastUnit = cfg.getHeads().get(0);
			
			for(Unit u:body.getUnits())
			{
				List<Unit> succ = cfg.getSuccsOf(u);
				if(succ.isEmpty())
				{
					lastUnit = u;
				}
				
			}
			
			Map<String, Map<String, Set<String>>> currmethod_out_sigma = currMethodOut.sigma;
			Set<String> currmethod_out_em = currMethodOut.escapeMap;
			
			Map<String, Map<String, Set<String>>> lastUnit_sigma = unitIn.get(lastUnit).sigma;
			Set<String> lastUnit_em = unitIn.get(lastUnit).escapeMap;
			
			boolean flag = compareMap(currmethod_out_sigma, lastUnit_sigma);
						
			if(!currmethod_out_em.equals(lastUnit_em) || !flag)
			{	
				currMethodOut.sigma = sigmaUnion(currmethod_out_sigma, lastUnit_sigma);
				currMethodOut.escapeMap = Sets.union(currmethod_out_em, lastUnit_em);
				
				OutSummary.put(currMethod, currMethodOut);
				
				Iterator<Edge> inEdges = cg.edgesInto(currMethod);				
	
				while(inEdges.hasNext())
				{
					Edge e = inEdges.next();
					
					SootMethod sourceMethod = e.getSrc().method();
					
					// we will not check condition targetMethod.equals(currMethod) to handle recursion
											
						interWorklist.add(sourceMethod);
											
				}
					
			}
			
			ArrayList<EscapeQuery> queries = A2.queryList;
			
			for(EscapeQuery query:queries)
			{
				
				// getting class and method names for which query is given
				String className = query.getClassName();
				String methodName = query.getMethodName();
				
				// checking the current class and method with query's class and method
				
				if(currClass_str.equals(className) && currMethod_str.equals(methodName))
				{	
					Set<String> intersect = new HashSet<>();
					
					// getting refs of left and right vars
					
					Synch sy = new Synch();
					
					if(synch.containsKey(className) && synch.get(className).containsKey(methodName))
						sy = synch.get(className).get(methodName);
					
					Set<String> st1 = new HashSet<>(sy.ref);
					Set<String> st2 = new HashSet<>(sy.emap);
					
					int ind = queries.indexOf(query);
					
					if(st1.contains("Og"))
					{
						A2.answers[ind] = "No";
					}
						
					
					else
					{
						boolean f = true;
						
						for(String s:st1)
						{
							if(st2.contains(s))
							{
								f = false;
								break;
							}
						}
						
						if(!f)
						{
							A2.answers[ind] = "No";
						}
							
						else
						{
							A2.answers[ind] = "Yes";
						}
							
					}
						
				}
			}
			
		}
		
	}
	
}
