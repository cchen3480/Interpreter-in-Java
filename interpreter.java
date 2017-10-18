import java.io.*;
import java.util.ArrayList;
import java.util.Stack;

public class interpreter {

	public static void interpreter(String input, String output) {
		FileReader fr = null;
		BufferedReader br = null;
		PrintWriter outWriter = null;
		File file = new File(output);
		ArrayList<unit> bindings = new ArrayList<unit>();
		Stack<thing> outStack = new Stack<thing>();
		ArrayList<environment> environstack = new ArrayList<environment>();
		environstack.add(new environment(bindings, outStack));
		Stack<String> currentenvironmentnamestack = new Stack<String>();
		currentenvironmentnamestack.push("original");
		int numoflets = 0;
		int read = 0;
		ArrayList<String> inputlist = new ArrayList<String>();
		try {
			outWriter = new PrintWriter(file);
		} catch (FileNotFoundException e1) {
			e1.printStackTrace();
		}
		try {
			fr = new FileReader(input);
			br = new BufferedReader(fr);
			String currentLine;
			String lines;
			while ((lines = br.readLine()) != null) {
				inputlist.add(lines);
			}
			while (read < inputlist.size()) {
				currentLine = inputlist.get(read++);
				System.out.println(currentLine);
				////////////////////////////////////////////////
				if (currentLine.contains("fun ")) {
					String[] parts = currentLine.split(" ");
					if (parts[0].equals("fun") && parts.length == 3) {
						thing funname = new thing(new name(parts[1]));
						thing param = new thing(new name(parts[2]));
						ArrayList<String> expressions = new ArrayList<String>();
						int numoffuns = 1;
						while (read < inputlist.size()) {
							expressions.add(currentLine);
							currentLine = inputlist.get(read++);
							if (currentLine.contains("fun ")) {
								numoffuns++;
							}
							if (currentLine.equals("funEnd")) {
								numoffuns--;
								if (numoffuns == 0) {
									expressions.add(currentLine);
									break;
								}
							}
						}
						expressions.remove(0);
						// got the list of expressions from fun
						Stack<thing> oristack = new Stack<thing>();
						ArrayList<unit> oribindings = new ArrayList<unit>(bindings);
						environment original = new environment(oribindings, oristack);
						closure c = new closure(original, param.n, expressions);
						bindings.add(0, new unit(funname.n, new thing(c)));
						outStack.push(new thing(new unit(funname.n, new thing(c))));
					} else
						outStack.push(new thing(new errorlit()));
				} else if (currentLine.contains("inOutFun ")) {
					String[] parts = currentLine.split(" ");
					if (parts[0].equals("inOutFun") && parts.length == 3) {
						thing funname = new thing(new name(parts[1]));
						thing param = new thing(new name(parts[2]));
						ArrayList<String> expressions = new ArrayList<String>();
						while (read < inputlist.size()) {
							expressions.add(currentLine);
							currentLine = inputlist.get(read++);
							if (currentLine.equals("funEnd")) {
								expressions.add(currentLine);
								break;
							}
						}
						expressions.remove(0);
						// got the list of expressions from fun
						Stack<thing> oristack = new Stack<thing>();
						ArrayList<unit> oribindings = new ArrayList<unit>(bindings);
						environment original = new environment(oribindings, oristack);
						closure c = new closure(original, param.n, expressions);
						c.isinout = true;
						bindings.add(0, new unit(funname.n, new thing(c)));
						outStack.push(new thing(new unit(funname.n, new thing(c))));
					} else
						outStack.push(new thing(new errorlit()));
				} else if (currentLine.equals("call")) {
					if (outStack.size() < 2) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing func = outStack.pop();
						thing arg = outStack.pop();
						if (func.isname) {
							boolean foundfun = false;
							boolean foundarg = false;
							int findfun = 0;
							for (; findfun < bindings.size(); findfun++) {
								if (func.n.val.equals(bindings.get(findfun).n.val)) {
									foundfun = true;
									break;
								}
							}
							if (foundfun && bindings.get(findfun).val.isclosure) {
								closure funclose = bindings.get(findfun).val.close;
								closure c = new closure(funclose.e, funclose.paraname, funclose.list);
								c.isinout = funclose.isinout;
								if (arg.isnum) {
									c.e.bindings.add(0, new unit(c.paraname, new thing(arg.num)));
									foundarg = true;
								}
								if (arg.isboollit) {
									c.e.bindings.add(0, new unit(c.paraname, new thing(arg.bool)));
									foundarg = true;
								}
								if (arg.isunit) {
									c.e.bindings.add(0, new unit(c.paraname, new thing(arg.u)));
									foundarg = true;
								}
								if (arg.isstr) {
									c.e.bindings.add(0, new unit(c.paraname, new thing(arg.s)));
									foundarg = true;
								}
								if (arg.isname) {
									c.argname = arg.n.val;
									thing val;
									boolean hassomething = false;
									for (int i = 0; i < bindings.size(); i++) {
										if (bindings.get(i).n.val.equals(arg.n.val)) {
											val = bindings.get(i).val;
											if (val.isnum) {
												c.e.bindings.add(0, new unit(c.paraname, new thing(val.num)));
												hassomething = true;
												foundarg = true;
											} else if (val.isboollit) {
												c.e.bindings.add(0, new unit(c.paraname, new thing(val.bool)));
												foundarg = true;
											} else if (val.isunit) {
												c.e.bindings.add(0, new unit(c.paraname, new thing(val.u)));
												hassomething = true;
												foundarg = true;
											} else if (val.isstr) {
												c.e.bindings.add(0, new unit(c.paraname, new thing(val.s)));
												hassomething = true;
												foundarg = true;
											} else if (val.isclosure) {
												c.e.bindings.add(0, new unit(c.paraname, new thing(val.close)));
												hassomething = true;
												foundarg = true;
											}
											break;
										}
									}
									if (hassomething == false) {
										c.e.bindings.add(0, new unit(c.paraname, new thing(arg.n)));
										foundarg = true;
									}
								}
								if (foundarg) {
									currentenvironmentnamestack.push(func.n.val);
									int t = read;
									ArrayList<String> templist = c.list;
									for (int l = 0; l < templist.size(); l++) {
										inputlist.add(t++, templist.get(l));
									}
									// -----------------------------------------------
									numoflets++;
									environment tempenv = new environment(new ArrayList<unit>(c.e.bindings),
											new Stack<>());
									environstack.add(tempenv);
									bindings = tempenv.bindings;
									outStack = tempenv.stack;
									bindings.add(0, new unit(new name(func.n.val), new thing(c)));

								} else {
									outStack.push(arg);
									outStack.push(func);
									outStack.push(new thing(new errorlit()));
								}
							} else {
								outStack.push(arg);
								outStack.push(func);
								outStack.push(new thing(new errorlit()));
							}
						} else {
							outStack.push(arg);
							outStack.push(func);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("return")) {
					numoflets--;
					int i = 0;
					String s = currentenvironmentnamestack.pop();
					for (; i < bindings.size(); i++) {
						if (bindings.get(i).n.val.equals(s)) {
							break;
						}
					}
					closure c = bindings.get(i).val.close;
					String arg = c.paraname.val;
					String outarg = c.argname;
					int findarg = 0;
					for (; findarg < bindings.size(); findarg++) {
						if (bindings.get(findarg).n.val.equals(arg)) {
							break;
						}
					}
					thing ofarg = bindings.get(findarg).val;
					thing fill = null;
					if (ofarg.isboollit)
						fill = new thing(ofarg.bool);
					else if (ofarg.isnum)
						fill = new thing(ofarg.num);
					else if (ofarg.isstr)
						fill = new thing(ofarg.s);
					else if (ofarg.iserrorlit)
						fill = new thing(ofarg.e);
					else if (ofarg.isname)
						fill = new thing(ofarg.n);
					bindings = environstack.get(numoflets).bindings;
					if (c.isinout) {
						bindings.add(0, new unit(new name(outarg), fill));
					}
					outStack = environstack.get(numoflets).stack;
					thing ret = environstack.get(numoflets + 1).stack.pop();
					if (ret.isboollit) {
						outStack.push(new thing(ret.bool));
					} else if (ret.isnum) {
						outStack.push(new thing(ret.num));
					} else if (ret.isstr) {
						outStack.push(new thing(ret.s));
					} else if (ret.isunit) {
						outStack.push(new thing(ret.u));
					} else if (ret.iserrorlit) {
						outStack.push(new thing(ret.e));
					} else if (ret.isname) {
						ArrayList<unit> tempbind = new ArrayList<unit>(environstack.get(numoflets + 1).bindings);
						boolean isunit = false;
						int yo = 0;
						for (; yo < tempbind.size(); yo++) {
							if (tempbind.get(yo).n.val.equals(ret.n.val)) {
								isunit = true;
								break;
							}
						}
						if (isunit) {
							thing ayo = tempbind.get(yo).val;
							if (ayo.isboollit) {
								outStack.push(new thing(new boollit(ret.bool.str)));
							} else if (ayo.isnum) {
								outStack.push(new thing(ayo.num));
							} else if (ayo.isstr) {
								outStack.push(new thing(ayo.s));
							} else if (ayo.isunit) {
								outStack.push(new thing(ayo.u));
							} else if (ayo.iserrorlit) {
								outStack.push(new thing(ayo.e));
							} else if (ayo.isclosure) {
								outStack.push(new thing(ret.n));
							}
						} else {
							outStack.push(new thing(ret.n));
						}
					}
					environstack.remove(environstack.size() - 1);
					while (!currentLine.equals("funEnd")) {
						currentLine = inputlist.get(read++);
					}
				} else if (currentLine.equals("funEnd")) {
					numoflets--;
					int i = 0;
					String s = currentenvironmentnamestack.pop();
					for (; i < bindings.size(); i++) {
						if (bindings.get(i).n.val.equals(s)) {
							break;
						}
					}
					closure c = bindings.get(i).val.close;
					String arg = c.paraname.val;
					String outarg = c.argname;
					int findarg = 0;
					for (; findarg < bindings.size(); findarg++) {
						if (bindings.get(findarg).n.val.equals(arg)) {
							break;
						}
					}
					thing ofarg = bindings.get(findarg).val;
					thing fill = null;
					if (ofarg.isboollit)
						fill = new thing(ofarg.bool);
					else if (ofarg.isnum)
						fill = new thing(ofarg.num);
					else if (ofarg.isstr)
						fill = new thing(ofarg.s);
					else if (ofarg.iserrorlit)
						fill = new thing(ofarg.e);
					else if (ofarg.isname)
						fill = new thing(ofarg.n);
					bindings = environstack.get(numoflets).bindings;
					if (c.isinout) {
						bindings.add(0, new unit(new name(outarg), fill));
					}
					bindings = environstack.get(numoflets).bindings;
					outStack = environstack.get(numoflets).stack;
				} else if (currentLine.equals("let")) {
					numoflets++;
					ArrayList<unit> tempbinding = new ArrayList<unit>(bindings);
					environment newenv = new environment(tempbinding, new Stack<thing>());
					environstack.add(numoflets, newenv);
					bindings = environstack.get(numoflets).bindings;
					outStack = environstack.get(numoflets).stack;
				} else if (currentLine.equals("end")) {
					numoflets--;
					bindings = environstack.get(numoflets).bindings;
					outStack = environstack.get(numoflets).stack;
					outStack.push(environstack.get(numoflets + 1).stack.pop());
					environstack.remove(environstack.size() - 1);
				} else if (currentLine.contains("push")) {
					String[] parts = currentLine.split(" ");
					String action = parts[0];
					if (action.equals("push")) {
						String tokens = "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ !@#$%^&*()_~+?><'|}{;";
						int len = parts.length;
						String value = "";
						if (len > 2) {
							for (int k = 1; k < len; k++) {
								value = value + parts[k] + " ";
							}
							value = value.substring(0, value.length() - 1);
						} else
							value = parts[1];
						if (isNum(value)) {
							int x = Integer.parseInt(value);
							thing a = new thing(x);
							outStack.push(a);
						} else {
							String n = value;
							for (int i = 0; i < value.length(); i++) {
								String cur = Character.toString(value.charAt(i));
								for (int j = 0; j < tokens.length(); j++) {
									if (Character.toString(tokens.charAt(j)).equals(cur)) {
										n = n.replace(cur, "");
										break;
									}
								}
							}
							if (n.equals("\"\"")) {
								thing t = new thing(new str(value));
								outStack.push(t);
							} else if (n.length() == 0 && Character.isLetter(value.charAt(0))) {
								thing th = new thing(new name(value));
								outStack.push(th);
							} else {
								outStack.push(new thing(new errorlit()));
							}
						}

					} else
						outStack.push(new thing(new errorlit()));
				} else if (currentLine.equals("pop"))
					if (outStack.size() == 0)
						outStack.push(new thing(new errorlit()));
					else
						outStack.pop();
				else if (currentLine.equals(":true:"))
					outStack.push(new thing(new boollit(":true:")));
				else if (currentLine.equals(":false:"))
					outStack.push(new thing(new boollit(":false:")));
				else if (currentLine.equals(":error:"))
					outStack.push(new thing(new errorlit()));
				else if (currentLine.equals("add")) {
					if (outStack.isEmpty() || outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda && foundb) {
							int res = x + y;
							thing str = new thing(res);
							outStack.push(str);
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("sub")) {
					if (outStack.isEmpty())
						outStack.push(new thing(new errorlit()));
					else if (outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {

						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda && foundb) {
							int res = y - x;
							thing str = new thing(res);
							outStack.push(str);
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}

				} else if (currentLine.equals("mul")) {
					if (outStack.isEmpty())
						outStack.push(new thing(new errorlit()));
					else if (outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;

								}
							}
						}
						if (founda && foundb) {
							int res = x * y;
							thing str = new thing(res);
							outStack.push(str);
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}

				} else if (currentLine.equals("div")) {
					if (outStack.isEmpty() || outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda && foundb) {
							if (x != 0) {
								int res = y / x;
								outStack.push(new thing(res));
							} else {
								outStack.push(b);
								outStack.push(a);
								outStack.push(new thing(new errorlit()));
							}
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("rem")) {
					if (outStack.isEmpty() || outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda && foundb) {
							if (x != 0) {
								int res = y % x;
								outStack.push(new thing(res));
							} else {
								outStack.push(b);
								outStack.push(a);
								outStack.push(new thing(new errorlit()));
							}
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("neg")) {
					if (outStack.isEmpty()) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						int x = 0;
						boolean founda = false;

						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda) {
							int res = x * -1;
							outStack.push(new thing(res));
						} else {
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("swap")) {
					if (outStack.isEmpty()) {
						outStack.push(new thing(new errorlit()));
					} else if (outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing x = outStack.pop();
						thing y = outStack.pop();
						outStack.push(x);
						outStack.push(y);
					}
				} else if (currentLine.equals("quit")) {
					break;
				} else if (currentLine.equals("and")) {
					if (outStack.isEmpty()) {
						outStack.push(new thing(new errorlit()));
					} else if (outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						String x = "";
						boolean founda = false;
						String y = "";
						boolean foundb = false;
						if (a.isboollit) {
							x = a.bool.str;
							founda = true;
						}
						if (b.isboollit) {
							y = b.bool.str;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isboollit) {
									founda = true;
									x = bindings.get(i).val.bool.str;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isboollit) {
									foundb = true;
									y = bindings.get(i).val.bool.str;
									break;
								}
							}
						}

						if (founda && foundb) {
							if (x.equals(":true:") && y.equals(":true:")) {
								outStack.push(new thing(new boollit(":true:")));
							} else {
								outStack.push(new thing(new boollit(":false:")));
							}
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("or")) {
					if (outStack.isEmpty()) {
						outStack.push(new thing(new errorlit()));
					} else if (outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						String x = "";
						boolean founda = false;
						String y = "";
						boolean foundb = false;
						if (a.isboollit) {
							x = a.bool.str;
							founda = true;
						}
						if (b.isboollit) {
							y = b.bool.str;
							foundb = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isboollit) {
									founda = true;
									x = bindings.get(i).val.bool.str;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isboollit) {
									foundb = true;
									y = bindings.get(i).val.bool.str;
									break;
								}
							}
						}
						if (founda && foundb) {
							if (x.equals(":true:") || y.equals(":true:")) {
								outStack.push(new thing(new boollit(":true:")));
							} else {
								outStack.push(new thing(new boollit(":false:")));
							}
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("not")) {
					if (outStack.isEmpty()) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						String x = "";
						boolean founda = false;
						if (a.isboollit) {
							x = a.bool.str;
							founda = true;
						}
						if (a.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isboollit) {
									founda = true;
									x = bindings.get(i).val.bool.str;
									break;
								}
							}
						}
						if (founda) {
							if (x.equals(":true:")) {
								outStack.push(new thing(new boollit(":false:")));
							} else {
								outStack.push(new thing(new boollit(":true:")));
							}
						} else {
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("equal")) {
					if (outStack.isEmpty() || outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {

							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda && foundb) {
							if (x == y) {
								outStack.push(new thing(new boollit(":true:")));
							} else
								outStack.push(new thing(new boollit(":false:")));
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("lessThan")) {
					if (outStack.isEmpty() || outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						int x = 0;
						boolean founda = false;
						int y = 0;
						boolean foundb = false;
						if (a.isnum) {
							x = a.num;
							founda = true;
						}
						if (b.isnum) {
							y = b.num;
							foundb = true;
						}
						if (a.isname) {

							for (int i = 0; i < bindings.size(); i++) {
								if (a.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									founda = true;
									x = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (b.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (b.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isnum) {
									foundb = true;
									y = bindings.get(i).val.num;
									break;
								}
							}
						}
						if (founda && foundb) {
							if (y < x) {
								outStack.push(new thing(new boollit(":true:")));
							} else
								outStack.push(new thing(new boollit(":false:")));
						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("bind")) {
					if (outStack.isEmpty()) {
						outStack.push(new thing(new errorlit()));
					} else if (outStack.size() == 1) {
						outStack.push(new thing(new errorlit()));
					} else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						if (b.isname) {
							int j = 0;
							for (; j < bindings.size(); j++) {
								if (b.n.val.equals(bindings.get(j).n.val)) {
									bindings.remove(j);
									break;
								}
							}
							if (a.isboollit) {
								unit x = new unit(b.n, new thing(new boollit(a.bool.str)));
								bindings.add(0, x);
								outStack.push(new thing(x));
							} else if (a.isnum) {
								unit x = new unit(b.n, new thing(a.num));
								bindings.add(0, x);
								outStack.push(new thing(x));
							} else if (a.isstr) {
								unit x = new unit(b.n, new thing(new str(a.s.val)));
								bindings.add(0, x);
								outStack.push(new thing(x));
							} else if (a.isname) {
								String aname = a.n.val;
								boolean found = false;
								int i = 0;
								for (; i < bindings.size(); i++) {
									unit q = bindings.get(i);
									if (aname.equals(q.n.val)) {
										found = true;
										break;
									}
								}
								if (found == true) {
									thing y = bindings.get(i).val;
									if (y.isboollit) {
										thing z = new thing(new boollit(y.bool.str));
										unit r = new unit(b.n, z);
										bindings.add(0, r);
										outStack.push(new thing(r));
									} else if (y.isname) {
										thing z = new thing(new name(y.n.val));
										unit r = new unit(b.n, z);
										bindings.add(0, r);
										outStack.push(new thing(r));
									} else if (y.isnum) {
										thing z = new thing(y.num);
										unit r = new unit(b.n, z);
										bindings.add(0, r);
										outStack.push(new thing(r));
									} else if (y.isstr) {
										thing z = new thing(new str(y.s.val));
										unit r = new unit(b.n, z);
										bindings.add(0, r);
										outStack.push(new thing(r));
									} else if (y.isunit) {
										thing z = new thing(y.u);
										unit r = new unit(b.n, z);
										bindings.add(0, r);
										outStack.push(new thing(r));
									} else {
										outStack.push(b);
										outStack.push(a);
										outStack.push(new thing(new errorlit()));
									}
								} else {
									outStack.push(b);
									outStack.push(a);
									outStack.push(new thing(new errorlit()));
								}
							} else if (a.isunit) {
								unit x = new unit(b.n, new thing(a.u));
								bindings.add(0, x);
								outStack.push(new thing(x));
							} else {
								outStack.push(b);
								outStack.push(a);
								outStack.push(new thing(new errorlit()));
							}

						} else {
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else if (currentLine.equals("if")) {
					if (outStack.size() < 3)
						outStack.push(new thing(new errorlit()));
					else {
						thing a = outStack.pop();
						thing b = outStack.pop();
						thing c = outStack.pop();
						boolean found = false;
						String boolstr = "";
						if (c.isboollit) {
							found = true;
							boolstr = c.bool.str;
						}
						if (c.isname) {
							for (int i = 0; i < bindings.size(); i++) {
								if (c.n.val.equals(bindings.get(i).n.val) && bindings.get(i).val.isboollit) {
									found = true;
									boolstr = bindings.get(i).val.bool.str;
									break;
								}
							}
						}
						if (found) {
							if (boolstr.equals(":true:")) {
								outStack.push(a);
							} else
								outStack.push(b);
						} else {
							outStack.push(c);
							outStack.push(b);
							outStack.push(a);
							outStack.push(new thing(new errorlit()));
						}
					}
				} else
					outStack.push(new thing(new errorlit()));
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			try {
				if (br != null)
					br.close();
				if (fr != null)
					fr.close();
			} catch (IOException ex) {
				ex.printStackTrace();
			}
		}
		while (outStack.size() != 0) {
			thing x = outStack.pop();
			if (x.isboollit) {
				outWriter.println(x.bool.str);
			} else if (x.isnum) {
				outWriter.println(x.num);
			} else if (x.iserrorlit) {
				outWriter.println(x.e.val);
			} else if (x.isunit) {
				outWriter.println(x.u.name);
			} else if (x.isname) {
				outWriter.println(x.n.val);
			} else if (x.isstr) {
				outWriter.println(x.s.val);

			}
		}
		outWriter.close();
	}

	public static boolean isNum(String str) {
		try {
			int d = Integer.parseInt(str);
		} catch (NumberFormatException nfe) {
			return false;
		}
		return true;
	}

}

class str {
	String val;

	str(String value) {
		value = value.replace("\"", "");
		this.val = value;
	}
}

class name {
	String val;

	name(String str) {
		this.val = str;
	}
}

class boollit {
	String str;

	boollit(String y) {
		this.str = y;
	}
}

class errorlit {
	String val = ":error:";
}

class unit {
	name n;
	thing val;
	String nameis;
	String valis;
	String name = ":unit:";

	unit(name n, thing val) {
		this.n = n;
		this.val = val;
		this.nameis = n.val;
		if (val.isboollit)
			this.valis = val.bool.str;
		else if (val.isname)
			this.valis = val.n.val;
		else if (val.isnum)
			this.valis = Integer.toString(val.num);
		else if (val.isstr)
			this.valis = val.s.val;
	}
}

class environment {
	ArrayList<unit> bindings;
	Stack<thing> stack;

	environment(ArrayList<unit> x, Stack<thing> y) {
		this.bindings = x;
		this.stack = y;
	}
}

class closure {
	thing ret;
	environment e;
	name paraname;
	ArrayList<String> list;
	boolean isinout = false;
	String argname;

	closure(environment original, name n, ArrayList<String> list) {
		this.e = original;
		this.paraname = n;
		this.list = list;
	}
}

class thing {
	boolean isclosure = false;
	boolean isstr = false;
	boolean isname = false;
	boolean iserrorlit = false;
	boolean isboollit = false;
	boolean isnum = false;
	boolean isunit = false;
	boolean isen = false;
	environment en;
	int num;
	str s;
	name n;
	errorlit e;
	boollit bool;
	unit u;
	closure close;

	thing(closure c) {
		this.close = c;
		isclosure = true;
	}

	thing(environment environ) {
		this.en = environ;
		this.isen = true;
	}

	thing(int rollno) {
		this.num = rollno;
		this.isnum = true;
	}

	thing(name n) {
		this.n = n;
		this.isname = true;
	}

	thing(errorlit e) {
		this.e = e;
		this.iserrorlit = true;
	}

	thing(boollit bool) {
		this.bool = bool;
		this.isboollit = true;
	}

	thing(unit rollno) {
		this.u = rollno;
		this.isunit = true;
	}

	thing(str st) {
		this.s = st;
		this.isstr = true;
	}
}