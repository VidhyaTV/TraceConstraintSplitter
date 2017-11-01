#Script to parse large smt files into smaller SMT files to run on Z3
import os
import re
import subprocess
import sys

from collections import deque

#Set-Location C:\Users\Vidhya\Documents\z3-4.4.1-x86-win\z3-4.4.1-x86-win\bin\
z3path='C:\\Users\\Vidhya\\Documents\\z3-4.4.1-x86-win\\z3-4.4.1-x86-win\\bin';
os.chdir(z3path);
#print(os.getcwd());#checking if current path was changed

loc='C:\\Users\Vidhya\Documents\PythonScripts';# location where input smt files are present in folders named 'runs'

programs = os.listdir(loc);#gets all entries/subelements in the directory as string names
#batchlength_array=[100,500,1000, 2000, 2500, 4000, 5000, 8000, 10000, 20000, 25000, 40000, 50000, 100000, 200000, 250000];
batchlength_array=[250000];
batchlength_array_Count=len(batchlength_array);
#print (batchlength_array_Count);

#highestcvalueplusone=27;
#epsilon=100;
highestcvalueplusone=22;
epsilon=100;

for batchlength in batchlength_array:
#{
	print ("Splitting constaints for batchlength={0}".format(batchlength))
	for program in programs:#for each sub-element(files+directories) in location-defined by loc variable
	#{
		if (os.path.isdir(os.path.join(loc, program)) and ("runs" in program)):#if sub-element is folder and contains the term 'runs'#create sub-element's full path using path join
		#{
			print('In folder '+program)
			sub_folder_path = os.path.join(loc, program) #get full path name of folder runs to go to files in it
			prog = os.listdir(sub_folder_path)			#files in runs folder
			
			file_counter=0;

			for const_file in prog:       #for each large smt/z3 constraint file in the folder
			#{
				if(('.smt2' in const_file) and ('altered' not in const_file)): #if it is not an altered smt file
				#if(($const_file.Name -cmatch '.smt2') -And ($const_file.Name -cnotmatch 'altered') -And ($file_counter -eq 0))#to run only on one input large z3 file
				#{
					#getting the path of the original constraint file
					orig_const_file_name_path = os.path.join(sub_folder_path, const_file)
					#getting the name of the original constraint file
					orig_const_file_name=const_file

					print("Processing input z3 file "+orig_const_file_name)
					
					#ranupto=10000001;
					ranupto=1000001;

                    #create folder for the altered files in parent 'runs' folder based on batchlength and number of the original constraint file
					new_folder_name=sub_folder_path+'\\run'+str(file_counter)+'\\batchlength'+str(batchlength);
					print(new_folder_name)
					if not os.path.exists(new_folder_name):
                    #{
						os.makedirs(new_folder_name)
                    #}
                
                    ####################CREATING ALL NEEDED FILES
					#creating the name of the new altered constraint files and creating those files
					
					#creating first file (0 to batchlength)
					
					#rfrom=j-batchlength;
					rfrom=0;
					#to=j+batchlength;
					to=batchlength+epsilon;
					const_file_altered_filename=orig_const_file_name+"_from"+ str(rfrom) +"_to"+str(to)+".smt2";
					altered_const_file_name_path = new_folder_name+'\\'+const_file_altered_filename;
					if not os.path.exists(altered_const_file_name_path):
					#{
						f=open(altered_const_file_name_path, "w")
						f.close()
						#print("Created new file"+altered_const_file_name_path)
						print("Created new file "+const_file_altered_filename)
					#}

					#creating remaining files
					
					for j in range(batchlength,ranupto,batchlength):
                    #{
						#rfrom=j-batchlength;
						rfrom=j-epsilon;
						#to=j+batchlength;
						to=j+batchlength+epsilon;
						const_file_altered_filename=orig_const_file_name+"_from"+ str(rfrom) +"_to"+str(to)+".smt2";
						altered_const_file_name_path = new_folder_name+'\\'+const_file_altered_filename;
						if not os.path.exists(altered_const_file_name_path):
						#{
							f=open(altered_const_file_name_path, "w")
							f.close()
							#print("Created new file"+altered_const_file_name_path)
							print("Created new file "+const_file_altered_filename)
						#}
                    #}

					file_counter=file_counter+1;#variable to create separate folder (name) for each run file

					prefix1="(declare-const"
					prefix2="(assert (or"

					files_in_new_folder_name = os.listdir(new_folder_name) #getting all sub-files

                    ####################PRINT all declaration CONSTRAINTS TO ALL FILES ###first to avoid referring to undefined variables 
                    #(our java xmltosmt parser script declares variables as it sees them so declaration can be spread in the input file)

					#for createdfile in files_in_new_folder_name:
					#{
					with open(orig_const_file_name_path) as infile:
						for line in infile:
							if prefix1 in line:
								for createdfile in files_in_new_folder_name:
									f=open(os.path.join(new_folder_name,createdfile), "a")
									f.write(line)
									f.close()
					#}
					
					####################PRINT all |l1-l2|<=epsilon CONSTRAINTS TO ALL FILES###
					#for createdfile in files_in_new_folder_name:
					#{
					with open(orig_const_file_name_path) as infile:
						for line in infile:
							if prefix2 in line:
								for createdfile in files_in_new_folder_name:
									f=open(os.path.join(new_folder_name,createdfile), "a")
									f.write(line)
									f.close()
					#}
					
					####################PRINT interval CONSTRAINTS TO respective FILES

					prefix5="(assert (!"
					prefix6="_msgAt" #message constraints should match prefix5 and prefix6
					print("writing message and interval constraints to respective files")
					
					with open(orig_const_file_name_path) as infile:
					#{
						for line in infile:
						#{
							if prefix5 in line:
							#{
								m1 = re.search('atl(\d+)', line)
								if m1: #if interval constraint
								#{
									#get interval endl
									endl=int(m1.group(1));                                  #is in l terms
									x=endl-(endl%batchlength);
									
									#################################
									xminuseps=(x-epsilon);
									xplusbeps=(x+batchlength+epsilon);
									xminusbeps=(x-batchlength-epsilon);
									xpluseps=(x+epsilon);
									xminusb=(x-batchlength);
									xminusbpluseps=(x-batchlength+epsilon);
									xminus2beps=(x-(2*batchlength)-epsilon);
									xminus2b=(x-(2*batchlength));
									xplusbminuseps=(x+batchlength-epsilon);
									xplus2beps=(x+(2*batchlength)+epsilon);

									#################################
									
									#file corresponding to current batch
									from_xminuseps="from"+str(xminuseps);
									to_xplusbeps="to"+str(xplusbeps);
									fromx="from"+str(x);#will be used if xminuseps is less than 0 #current file starts at 0
									
									#file corresponding to previous file
									from_xminusbeps="from"+str(xminusbeps);
									to_xpluseps="to"+str(xpluseps);
									from_xminusb="from"+str(xminusb);#will be used if xminusbeps is less than 0 #previous file starts at 0
																		
									tox="to"+str(x);

									#file corresponding to previous-previous batch
									to_xminusbpluseps="to"+str(xminusbpluseps);
									from_xminus2beps="from"+str(xminus2beps);
									from_xminus2b="from"+str(xminus2b);#will be used if xminus2beps is less than 0 #previous-previous file starts at 0
									
									#file corresponding to next batch
									from_xplusbminuseps="from"+str(xplusbminuseps);
									to_xplus2beps="to"+str(xplus2beps);
									
									#tentimesx = 10*x;
									tentimesx = highestcvalueplusone*x; #highest c value was 26 then * by 27
									tentimeseps=highestcvalueplusone*epsilon;
									tentimesb=highestcvalueplusone*batchlength;

									#get interval actual startl,
									startl=0;									
									m2 = re.search('\(=> \(and \(<= (\d+)', line)
									if m2:
									#{
										#$startl=$matches[1];                           #is in ((10*l)+c) terms
										startl=int(m2.group(1));                             #is in ((27*l)+c) terms
									#}
									
									#get interval actual endl,
									actualendlinconstraint=0;
									m3 = re.search('(\d+)\)\) \(and \(=', line)
									if m3:
									#{
										#Write-Host "actual endl in constraint extracted"
										actualendlinconstraint = int(m3.group(1));
									#}
									
									#if ((actualendlinconstraint < x) or (actualendlinconstraint != endl*highestcvalueplusone)):#incorrect because 'endl'doesnt account for c in <l,c>
									if ((actualendlinconstraint < x*highestcvalueplusone) or (actualendlinconstraint < (endl*highestcvalueplusone)) or (actualendlinconstraint > ((endl*highestcvalueplusone)+highestcvalueplusone))):#x is leftend/minimum value in the batch so actualendlinconstraint has to be >= x not less
									#if ((actualendlinconstraint < x*highestcvalueplusone) or (actualendlinconstraint < (endl*highestcvalueplusone))):#x is leftend/minimum value in the batch so actualendlinconstraint has to be >= x not less
									#{
										print("Error state, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , endl is "+str(endl));
										sys.exit();
									#}
									else:
									#{
										if (actualendlinconstraint<((xpluseps)*highestcvalueplusone)): #3
										#{
											##############first write constraint to previous file (common to #4, #5, #6)
											if (xminusbeps >= 0 ):
												for createdfile in files_in_new_folder_name:
												#{
													if((from_xminusbeps in createdfile) and (to_xpluseps in createdfile)):
													#{
														f=open(os.path.join(new_folder_name,createdfile), "a")
														f.write(line)
														f.close()
													#}
												#}
											elif (xminusb >= 0 ):#previous file starts at 0
												for createdfile in files_in_new_folder_name:
												#{
													if((from_xminusb in createdfile) and (to_xpluseps in createdfile)):
													#{
														f=open(os.path.join(new_folder_name,createdfile), "a")
														f.write(line)
														f.close()
													#}
												#}
											else:
												#no previous file so do nothing
												pass
											#####4
											if (startl < ((xminusbpluseps)*highestcvalueplusone)): #4
											#{
												if (xminuseps >= 0):
												#{
													#change start to x-eps and write to current file
													constraint1=line;
													constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												#}
												else: #current file starts at 0
												#{
													#cannot happen because the startl is in the previous batch and there is no -ve batch
													print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
												#}
												
												#change end to x-b+eps and write to previous-previous file											
												if (xminus2beps >=0):
												#{
													constraint1=line;
													constraint1=constraint1.replace(str(actualendlinconstraint),str((xminusbpluseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminus2beps in createdfile) and (to_xminusbpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												#}
												elif (xminus2b >=0):#previous-previous file starts at 0
												#{
													constraint1=line;
													constraint1=constraint1.replace(str(actualendlinconstraint),str((xminusbpluseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminus2b in createdfile) and (to_xminusbpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												#}
												else:#previous-previous file does not exist so do nothing
													pass
											#}
											elif (startl < ((xminuseps)*highestcvalueplusone)):#5
											#{
												if ((xminuseps) >= 0):
												#{
													#change start to x-eps and write to current file
													constraint1=line;
													constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												#}
												else: #current file starts at 0
												#{
													#cannot happen because the startl is in the previous batch and there is no -ve batch
													print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
												#}
											#}
											else:#6  or start also in #3
											#{
												if (xminuseps) >= 0:
												#{
													#write to current file
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												#}
												elif ((startl >= x*highestcvalueplusone) and (x==0)): # should be case where start is also in #3 AND x ==0
												#{
													#write to current file #starts at 0
													for createdfile in files_in_new_folder_name:
													#{
														if((fromx in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												#}
												else: #case #6 and current file starts at 0
												#{
													#cannot happen because the startl is in the previous batch and there is no -ve batch
													print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
												#}
											#}
										#}
										elif (actualendlinconstraint<((xplusbminuseps)*highestcvalueplusone)): #2
										#{
											if (startl > ((xpluseps)*highestcvalueplusone)):#startl also in #2
											#{
												if ((xminuseps)>=0):
												#{
													#only write to current file
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												#}
												elif x==0:
													#only write to current file
													for createdfile in files_in_new_folder_name:
													#{
														if((fromx in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												else:
													#cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon,
													print("Error state:cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
											#}
											else:#startl not in #2
											#{
												#change end to x+eps and write to previous file												
												if ((xminusbeps) >= 0 ):
													constraint1=line;
													constraint1=constraint1.replace(str(actualendlinconstraint),str((xpluseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminusbeps in createdfile) and (to_xpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												elif ((xminusb) >= 0 ):#previous file starts at 0
													constraint1=line;
													constraint1=constraint1.replace(str(actualendlinconstraint),str((xpluseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminusb in createdfile) and (to_xpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												else:
													#no previous file so do nothing
													pass												
												
												if (startl < ((xminusbpluseps)*highestcvalueplusone)): #4
												#{
													if ((xminuseps)>=0):
														#change start to x-eps and write to current file
														constraint1=line;
														constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													elif x==0:
														#change start to x-eps and write to current file
														constraint1=line;
														constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((fromx in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													else:
														#cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon,
														print("Error state:cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
														sys.exit();

													#change end to x-b+epsand write to previous-previous file
													if ((xminus2beps)>=0):
														constraint1=line;
														constraint1=constraint1.replace(str(actualendlinconstraint),str((xminusbpluseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminus2beps in createdfile) and (to_xminusbpluseps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													elif ((xminus2b)>=0):
														constraint1=line;
														constraint1=constraint1.replace(str(actualendlinconstraint),str((xminusbpluseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminus2b in createdfile) and (to_xminusbpluseps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													else:#previous-previous file does not exist
														pass #do nothing
												#}
												elif (startl < ((xminuseps)*highestcvalueplusone)):#5
												#{
													if ((xminuseps) >= 0):
													#{
														#change start to x-eps and write to current file
														constraint1=line;
														constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													#}
													else: #current file starts at 0
													#{
														#cannot happen because the startl is in the previous batch and there is no -ve batch
														print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
														sys.exit();
													#}
												#}
												else:#start in #6 or start in #3
												#{
													if ((xminuseps) >= 0):
													#{
														#write to current file
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(line)
																f.close()
															#}
														#}
													#}
													elif ((startl >= x*highestcvalueplusone) and (x==0)): # should be case where start is also in #3 AND x ==0
													#{
														#write to current file #starts at 0
														for createdfile in files_in_new_folder_name:
														#{
															if((fromx in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(line)
																f.close()
															#}
														#}
													#}
													else: #case #6 and current file starts at 0
													#{
														#cannot happen because the startl is in the previous batch and there is no -ve batch
														print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
														sys.exit();
													#}
												#}
											#}
										#}
										else: #1
										#{
											if (startl > ((xplusbminuseps)*highestcvalueplusone)):#start also in #1
											#{
												#write to current and next file
												if ((xminuseps) >=0):
													for createdfile in files_in_new_folder_name:
													#{
														if(((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)) or ((from_xplusbminuseps  in createdfile) and (to_xplus2beps in createdfile))):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												elif x==0:
													for createdfile in files_in_new_folder_name:
													#{
														if(((fromx in createdfile) and (to_xplusbeps in createdfile)) or ((from_xplusbminuseps  in createdfile) and (to_xplus2beps in createdfile))):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												else:
													#cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon,
													print("Error state:cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
											#}
											elif (startl > ((xpluseps)*highestcvalueplusone)): #start in #2
											#{
												#write to current file
												if ((xminuseps) >=0):
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												elif (x==0):
													for createdfile in files_in_new_folder_name:
													#{
														if((fromx in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												else:
													#cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon,
													print("Error state:cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
												#change start to x+b-eps and write to next file
												constraint1=line;
												constraint1=constraint1.replace(str(startl),str((xplusbminuseps)*highestcvalueplusone));
												for createdfile in files_in_new_folder_name:
												#{
													if((from_xplusbminuseps  in createdfile) and (to_xplus2beps in createdfile)):
													#{
														f=open(os.path.join(new_folder_name,createdfile), "a")
														f.write(constraint1)
														f.close()
													#}
												#}
											#}
											else:
											#{
												######common to start in 4,5,6
												#change end to x+eps and write to previous file
												if ((xminusbeps)>=0):
													constraint1=line;
													constraint1=constraint1.replace(str(actualendlinconstraint),str((xpluseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminusbeps in createdfile) and (to_xpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												elif ((xminusb) >=0):#previous file starts at 0
													constraint1=line;
													constraint1=constraint1.replace(str(actualendlinconstraint),str((xpluseps)*highestcvalueplusone));
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminusb in createdfile) and (to_xpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												elif ((startl >= x*highestcvalueplusone) and (x==0)):# startl should be in #3 (#2,#1 were already handled), x==0 and #previous file does not exist
													pass#so do nothing
												else:
												#{
													#cannot happen because the startl is in the previous batch (cases #4#5#6) and there is no -ve batch
													print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
													sys.exit();
												#}
												#change start to x+b-eps and write to next file
												constraint1=line;
												constraint1=constraint1.replace(str(startl),str((xplusbminuseps)*highestcvalueplusone));
												for createdfile in files_in_new_folder_name:
												#{
													if((from_xplusbminuseps  in createdfile) and (to_xplus2beps in createdfile)):
													#{
														f=open(os.path.join(new_folder_name,createdfile), "a")
														f.write(constraint1)
														f.close()
													#}
												#}
												if (startl < ((xminusbpluseps)*highestcvalueplusone)): #4
												#{
													#change end to x-b+eps and write to previous-previous file
													if ((xminus2beps) >=0):
														constraint1=line;
														constraint1=constraint1.replace(str(actualendlinconstraint),str((xminusbpluseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminus2beps in createdfile) and (to_xminusbpluseps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													elif ((xminus2b) >=0):#previous-previous file starts at 0
														constraint1=line;
														constraint1=constraint1.replace(str(actualendlinconstraint),str((xminusbpluseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminus2b in createdfile) and (to_xminusbpluseps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													else:#no previous previous file
														pass #so do nothing
													#change start to x-eps and write to current file
													constraint1=line;
													constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
													#write to current file
													for createdfile in files_in_new_folder_name:
													#{
														if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(constraint1)
															f.close()
														#}
													#}
												#}
												elif (startl < ((xminuseps)*highestcvalueplusone)):#5
												#{
													if (xminuseps) >= 0:
													#{
														#change start to x-eps and write to current file
														constraint1=line;
														constraint1=constraint1.replace(str(startl),str((xminuseps)*highestcvalueplusone));
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(constraint1)
																f.close()
															#}
														#}
													#}
													else: #current file starts at 0
													#{
														#cannot happen because the startl is in the previous batch and there is no -ve batch
														print("Error state:cannot happen because the startl is in the previous batch and there is no -ve batch, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
														sys.exit();
													#}
												#}
												else:#startl < (xpluseps):#start in #6 or start  in #3
												#{
													#write to current file
													if ((xminuseps) >=0):
													#{
														for createdfile in files_in_new_folder_name:
														#{
															if((from_xminuseps in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(line)
																f.close()
															#}
														#}
													#}
													elif ((x==0) and (startl >= x*highestcvalueplusone)): # startl should be #3 if previous batch does not exist
													#{
														for createdfile in files_in_new_folder_name:
														#{
															if((fromx in createdfile) and (to_xplusbeps in createdfile)):
															#{
																f=open(os.path.join(new_folder_name,createdfile), "a")
																f.write(line)
																f.close()
															#}
														#}
													#}
													else:
													#{
														#cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon,
														print("Error state:cannot happen because the only other option is (0<x<epsilon) and x grows in steps of batchlength size and minimum value of batchlength is epsilon, the value of actualendlinconstraint is "+str(actualendlinconstraint)+" , x is "+str(x)+" , startl is "+str(startl));
														sys.exit();
													#}
												#}
											#}
										#}
									#}
								#}
								####################PRINT message CONSTRAINTS TO respective FILES
								elif prefix6 in line: #if message constraint (matches prefix 5 and 6)
								#{
									m4 = re.search('at_l(\d+)_at', line)
									if m4:
									#Write-Host "message constraint"
									#{
										recvl=int(m4.group(1)); 
										mx=recvl-(recvl%batchlength);
										
										#################################
										mxminuseps=(mx-epsilon);
										mxplusbeps=(mx+batchlength+epsilon);
										mxminusbeps=(mx-batchlength-epsilon);
										mxpluseps=(mx+epsilon);
										mxminusb=(mx-batchlength);
										mxplusbminuseps=(mx+batchlength-epsilon);
										mxplus2beps=(mx+(2*batchlength)+epsilon);

										#################################
										from_mxminuseps="from"+str(mxminuseps);
										to_mxplusbeps="to"+str(mxplusbeps);
										from_mxminusbeps="from"+str(mxminusbeps);
										to_mxpluseps="to"+str(mxpluseps);
										from_mxminusb="from"+str(mxminusb);
										from_mxplusbminuseps="from"+str(mxplusbminuseps);
										to_mxplus2beps="to"+str(mxplus2beps);
										from_mx="from"+str(mx);
										to_mx="to"+str(mx);
										
										if (mx>0):
										#{
											#write to current file
											for createdfile in files_in_new_folder_name:
											#{
												if((from_mxminuseps in createdfile) and (to_mxplusbeps in createdfile)):
												#{
													f=open(os.path.join(new_folder_name,createdfile), "a")
													f.write(line)
													f.close()
												#}
											#}
											if (recvl > (mxplusbminuseps)):
											#{
												#write to next file
												for createdfile in files_in_new_folder_name:
												#{
													if((from_mxplusbminuseps  in createdfile) and (to_mxplus2beps in createdfile)):
													#{
														f=open(os.path.join(new_folder_name,createdfile), "a")
														f.write(line)
														f.close()
													#}
												#}
											#}
											elif (recvl < mxpluseps):
											#{
												#write to previous file
												if (mxminusbeps>=0):
												#{	
													for createdfile in files_in_new_folder_name:
													#{
														if((from_mxminusbeps in createdfile) and (to_mxpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												#}
												elif ((mxminusb>=0) and (mx==batchlength)):#previous file starts at 0#if (mx==batchlength):#just checking if it the correct case
												#{
													for createdfile in files_in_new_folder_name:
													#{
														if((from_mxminusb in createdfile) and (to_mxpluseps in createdfile)):
														#{
															f=open(os.path.join(new_folder_name,createdfile), "a")
															f.write(line)
															f.close()
														#}
													#}
												#}
												else:
												#{
													print("Error state: mx > 0 and mx-batchlength is not even 0? Not possible because mx grows in steps of batchlength size");
													sys.exit();
												#}
											#}
											else:
											#{
												pass
											#}
										#}
										elif (mx==0):
										#{
											#write to file {0 to batchlength+eps}
											from_zero="from"+str(0);
											to_beps="to"+str(batchlength+epsilon);
											for createdfile in files_in_new_folder_name:
											#{
												if((from_zero in createdfile) and (to_beps in createdfile)):
												#{
													f=open(os.path.join(new_folder_name,createdfile), "a")
													f.write(line)
													f.close()
												#}
											#}
											if (recvl > batchlength-epsilon):
											#{
												#write to file {batchlength-epsilon to 2*batchlength+epsilon}
												from_bminuseps="from"+str(batchlength-epsilon);
												to_2beps="to"+str((2*batchlength)+epsilon);
												for createdfile in files_in_new_folder_name:
												#{
													if((from_bminuseps in createdfile) and (to_2beps in createdfile)):
													#{
														f=open(os.path.join(new_folder_name,createdfile), "a")
														f.write(line)
														f.close()
													#}
												#}
											#}
											else:
											#{
												pass
											#}
										#}
										else:
										#{
											print("Code that should not execute");
											sys.exit();
										#}
									#}
									else:
									#{
										print("COULD NOT IDENTIFY TIMESTAMP OF CONSTRAINT")
									#}
								#}
							#}
						#}
					#}
					
					####################PRINT CONSTRAINTS for bounds for l
					
					#########UPPERBOUND
					print("Printing upperbounds of l by scanning contents of created file")
					for createdfile in files_in_new_folder_name:
                    #{
						print("Writing to file "+createdfile)
						fnm=createdfile;
						#upperbound=0;
						m5 = re.search('to(\d+)', fnm)
						if m5:
						#{
							upperbound=m5.group(1);
						#}
						if((ranupto-1) < int(upperbound)):
						#{
							#(following will work because the tail 10 lines in the last file of the batch will have tail 10 lines of the original large constraint file- one line per process )
							with open(os.path.join(new_folder_name,createdfile)) as fin:
								last10 = deque(fin, 10)
								for eachline in last10:
									if prefix5 in eachline:#add lower bound for l corresponding to all 10 processes 
									#{
										print("Tail element "+eachline)
										processid = 0;
										m6 = re.search('interval_(\d)', eachline)
										if m6:
										#{
											processid=m6.group(1);
											#print("Processid:"+processid)
											m7 = re.search('(\d+)\)\)\s\(and\s\(=', eachline)
											if m7:
											#{
												l=m7.group(1);
												output="(assert (<= l"+processid+" "+l+"))\n";
												f=open(os.path.join(new_folder_name,createdfile), "a")
												f.write(output)
												f.close()
											#}
										#}
									#}
						#}
						else:
						#{
							upperbound=int(upperbound)*10;
							#upperbound=int(upperbound)*27;

							for i in range(0,10,1):
							#{
								f=open(os.path.join(new_folder_name,createdfile), "a")
								f.write("(assert (<= l"+str(i)+" "+str(upperbound)+"))\n")
								f.close()
							#}
						#}
                    #}
 
                    #####LOWERBOUND
					print("Printing Lowerbounds of l by scanning contents of created file")
					
					for createdfile in files_in_new_folder_name:
                    #{
						array_of_lower_bound_visited_processes= [];
						with open((os.path.join(new_folder_name,createdfile))) as infile:
						#{
							for line in infile:
							#{
								if((prefix5 in line) and (len(array_of_lower_bound_visited_processes) < 11)):#add lower bound for l corresponding to all 10 processes
								#{
									#Write-Host "Size of array_of_lower_bound_visited_processes is "$array_of_lower_bound_visited_processes.Count
									processid = 0;
									m8 = re.search('interval_(\d)', line)
									if m8:
									#{
										processid=m8.group(1);
										#Write-Host "Processid:"$processid
										if processid not in array_of_lower_bound_visited_processes:
										#{
											#add process to lower_bound_visited_array
											array_of_lower_bound_visited_processes.append(processid);
											#Write-Host "Size of array_of_lower_bound_visited_processes is "$array_of_lower_bound_visited_processes.Count
											m9 = re.search('\(=> \(and \(<= (\d+)', line)
											if m9:#get lower bound
											#{
												l=m9.group(1);
												output="(assert (>= l"+processid+" "+l+"))\n";
												f=open(os.path.join(new_folder_name,createdfile), "a")
												f.write(output)
												f.close()
												#$output | Add-Content $createdfile.FullName #write constraint to the selected file
											#}
										#}
									#}
								#}
							#}   
						#}
                    #}
					
					####################PRINT predicate to be detected and check-sat TO ALL FILES
					print("Printing predicate to detect and check-sat")
					prefix3="(assert (and ";
					prefix4="(check-sat)";

					with open(orig_const_file_name_path) as infile:
						for line in infile:
							if ((prefix3 in line) or (prefix4 in line)):
								for createdfile in files_in_new_folder_name:
									f=open(os.path.join(new_folder_name,createdfile), "a")
									f.write(line)
									f.close()

					output_file = new_folder_name+'\z3output.txt'
					if os.path.exists(output_file):
                    #{
						os.remove(new_folder_name)
                    #}

					##################running generated z3 batch files on Z3
					
					for createdfile in files_in_new_folder_name:
                    #{
						if(('.smt2' in createdfile) and ('altered' not in createdfile)):
                        #{
                            #creating the name and path of the new altered constraint file
							altered_small_const_file_name=createdfile + "_altered.smt2";
							altered_small_const_file_name_path = new_folder_name+"\\"+altered_small_const_file_name

                            #removing constraint names to avoid duplicate constraint name error
							with open(os.path.join(new_folder_name,createdfile)) as infile:
							#{
								fi=open(altered_small_const_file_name_path, "a")
								for line in infile:
								#{
									new_line=line.replace("(!", "");
									newer_line=re.sub(":named.*", ")", new_line);
									fi.write(newer_line)
								#}
								fi.close()
							#}
                            #running each small z3 file 3 times
							for i in range(1,4,1):
                            #{
								#running the constraint file on z3
								fname = '\n Z3 result for file '+createdfile+'; Z3 Run:'+str(i)+'\n'								
								with open(output_file, "a") as log_file:
									log_file.write(fname)
									subprocess.call([".\\z3.exe",altered_small_const_file_name_path], stdout=log_file,stderr=log_file)
								print("Running " +altered_small_const_file_name+ "on Z3 done")
                            #}
                        #}
                    #}#end of z3 running
					
				#}##end of if(smt and unaltered file)
            #}#end of for each large z3 constraint file
        #}#end of #if folder-name contains the term 'runs'
    #}#end of #for each sub-element(files+directories) in location-defined by loc variable
#}#end of batchlengtharray for-loop