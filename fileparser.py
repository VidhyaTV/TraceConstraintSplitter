#Script to parse large smt files into smaller SMT files to run on Z3
import os
import re
import subprocess

from collections import deque

#Set-Location C:\Users\Vidhya\Documents\z3-4.4.1-x86-win\z3-4.4.1-x86-win\bin\
z3path='C:\\Users\\Vidhya\\Documents\\z3-4.4.1-x86-win\\z3-4.4.1-x86-win\\bin';
os.chdir(z3path);
#print(os.getcwd());#checking if current path was changed

loc='C:\\Users\Vidhya\Documents\PythonScripts';# location where input smt files are present in folders named 'runs'

programs = os.listdir(loc);#gets all entries/subelements in the directory as string names

batchlength_array=[50000];
batchlength_array_Count=len(batchlength_array);
#print (batchlength_array_Count);

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
					
					ranupto=10000001;
					#ranupto=100001;

                    #create folder for the altered files in parent 'runs' folder based on batchlength and number of the original constraint file
					new_folder_name=sub_folder_path+'\\run'+str(file_counter)+'\\batchlength'+str(batchlength);
					print(new_folder_name)
					if not os.path.exists(new_folder_name):
                    #{
						os.makedirs(new_folder_name)
                    #}
                
                    ####################CREATING ALL NEEDED FILES

                    #creating the name of the new altered constraint file
					for j in range(batchlength,ranupto,batchlength):
                    #{
						rfrom=j-batchlength;
						to=j+batchlength;
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
					prefix6="_msgAt"
					print("writing message and interval constraints to respective files")
					
					with open(orig_const_file_name_path) as infile:
					#{
						for line in infile:
						#{
							if prefix5 in line:
							#{
								m1 = re.search('atl(\d+)', line)
								if m1:
								#{
									#get interval endl
									endl=int(m1.group(1));                                  #is in l terms
									x=endl-(endl%batchlength);

									xminusb="from"+str(x-batchlength);
									xminustwob="from"+str(x-(2*batchlength));
									xplusb="to"+str(x+batchlength);
									xplustwob="to"+str(x+(2*batchlength));
									fromx="from"+str(x);
									tox="to"+str(x);

									#tentimesx = 10*x;
									tentimesx = 27*x;

									#get interval endl startl,
									startl=0;									
									m2 = re.search('\(=> \(and \(<= (\d+)', line)
									if m2:
									#{
										#$startl=$matches[1];                           #is in ((10*l)+c) terms
										startl=int(m2.group(1));                             #is in ((27*l)+c) terms
									#}
									if startl < tentimesx: 
									#{
										#Write-Host 'starttl: '$startl' is less than tentimesx:'$tentimesx
										actualendlinconstraint=0;
										m3 = re.search('(\d+)\)\) \(and \(=', line)
										if m3:
										#{
											#Write-Host "actual endl in constraint extracted"
											actualendlinconstraint = m3.group(1);
										#}
										#split constraint at $tentimesx
										constraint1=line;
										constraint1=constraint1.replace(actualendlinconstraint,str(tentimesx));

										if startl != 0:
										#{
											constraint2=line;
											constraint2=constraint2.replace(str(startl),str(tentimesx));
										#}
										else:
										#{
											constraint2=line;
											piecetoreplace="(<= 0";
											newpiece="(<= "+str(tentimesx);
											constraint2=constraint2.replace(piecetoreplace,newpiece);                            
										#}

										#printing constraint1
										for createdfile in files_in_new_folder_name:
										#{
											if(((xminusb in createdfile) and (xplusb in createdfile)) or ((xminustwob in createdfile) and (tox in createdfile))):
											#{
												#Write-Host "Writing "$constraint1" to "$createdfile.BaseName
												#$constraint1| Add-Content $createdfile.FullName #write constraint to the selected file
												f=open(os.path.join(new_folder_name,createdfile), "a")
												f.write(constraint1)
												f.close()
											#}
										#}
										#printing constraint2
										for createdfile in files_in_new_folder_name:
										#{
											if(((xminusb in createdfile) and (xplusb in createdfile)) or ((fromx in createdfile) and (xplustwob in createdfile))):
											#{
												#Write-Host "Writing "$constraint2" to "$createdfile.BaseName
												#$constraint2 | Add-Content $createdfile.FullName #write constraint to the selected file
												f=open(os.path.join(new_folder_name,createdfile), "a")
												f.write(constraint2)
												f.close()
											#}
										#}
									#}
									else:
									#{
										#Write-Host 'starttl '$startl' greater than tentimesx:'$tentimesx
										for createdfile in files_in_new_folder_name:
										#{
											if(((xminusb in createdfile) and (xplusb in createdfile)) or ((fromx in createdfile) and (xplustwob in createdfile))):
											#{
												#Write-Host "Writing constraint as it is "$_
												#$_ | Add-Content $createdfile.FullName #write constraint to the selected file
												f=open(os.path.join(new_folder_name,createdfile), "a")
												f.write(line)
												f.close()
											#}
										#}
									#}
								#}
								####################PRINT message CONSTRAINTS TO respective FILES
								elif prefix6 in line:
								#{
									m4 = re.search('at_l(\d+)_at', line)
									if m4:
									#Write-Host "message constraint"
									#{
										recvl=int(m4.group(1)); 
										x=recvl-(recvl%batchlength);

										xminusb="from"+str(x-batchlength);
										xminustwob="from"+str(x-(2*batchlength));
										xplusb="to"+str(x+batchlength);
										xplustwob="to"+str(x+(2*batchlength));
										fromx="from"+str(x);
										tox="to"+str(x);

										#Write-Host "Computed x as "$x
										for createdfile in files_in_new_folder_name:
										#{
											if(((xminusb in createdfile) and (xplusb in createdfile)) or ((fromx in createdfile) and (xplustwob in createdfile))):
											#{
												#Write-Host "Writing message constraint"$_
												#$_ | Add-Content $createdfile.FullName #write constraint to the selected file
												f=open(os.path.join(new_folder_name,createdfile), "a")
												f.write(line)
												f.close()
											#}
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
					
					
					#########UPPERBOUND
					print("Printing upperbounds of l by scanning contents of created file")
					for createdfile in files_in_new_folder_name:
                    #{
						print("Writing to file "+createdfile)
						fnm=createdfile;
						upperbound=0;
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
							#upperbound=int(upperbound)*10;
							upperbound=int(upperbound)*27;

							for i in range(0,10,1):
							#{
								f=open(os.path.join(new_folder_name,createdfile), "a")
								f.write("(assert (<= l"+str(i)+" "+str(upperbound)+"))\n")
								f.close()
							#}
						#}
                    #}
					####################PRINT CONSTRAINTS for bounds for l
 
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
								fname = 'Z3 result for file '+createdfile+'; Z3 Run:'+str(i)								
								with open(output_file, "a") as log_file:
									log_file.write(fname)
									subprocess.call([".\\z3.exe",altered_small_const_file_name_path], stdout=log_file)
								print("Running " +altered_small_const_file_name+ "on Z3 done")
                            #}
                        #}
                    #}#end of z3 running
					
				#}##end of if(smt and unaltered file)
            #}#end of for each large z3 constraint file
        #}#end of #if folder-name contains the term 'runs'
    #}#end of #for each sub-element(files+directories) in location-defined by loc variable
#}#end of batchlengtharray for-loop