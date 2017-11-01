import os
import re
#for each folder in runs folder
loc=os.getcwd();#get current working directory location #assumption is that this script is placed in the 'runs' folder
programs = os.listdir(loc);#get all entries/elements in the directory
for program in programs:
#{
	#get program(e.g.batch100) folder path
	batch_folder_path=os.path.join(loc,program);
	#if its name does not correspond to batchlength50000 or batchlength100000 or batchlength 200000#these were created using corrected scripts so nothing to correct
	if ((os.path.isdir(batch_folder_path)) and ('batchlength50000' not in program) and ('batchlength100000' not in program) and ('batchlength200000' not in program)):#get only subdirectories
	#{
		#for each smt file in this folder that does not have a filename that contain 'from0_to' or 'from100_to' or 'from200_to' #because these files were corrected manually
		files=os.listdir(batch_folder_path);
		for file in files:
		#{
			#if (('.smt2' in file) and ('from0_to' not in file) and ('from100_to' not in file) and ('from200_to' not in file)):
			#above if not needed because 'assert(<= l' occurs only in upperbound constraint, so this value gets replaced on in those constraints
			#if (('.smt2' in file) and ('altered' in file)): #correct only in altered files to save time
			if ('.smt2' in file):#correct all smt files
			#{
				#get the file name and the upperbound value from the file name: this upperbound value in terms of l
				m1=re.search('to(\d+)',file);
				if (m1):
				#{
					upperbound= int(m1.group(1));
					#search and replace all occurances of this upperbound*10 value with upperbound*22
					#i.e. read line by line and if line contains '(assert (<= l' => then replace str(upperbound*10) value with str(upperbound*22)
					org_altered_file_path=os.path.join(batch_folder_path,file);
					correctedfile=file.replace('.smt2_from','_from');
					correctedfile=correctedfile.replace('.smt2_altered','_altered');
					correctedfile='nw_'+ correctedfile;
					correctedfile_path=os.path.join(batch_folder_path,correctedfile);
					with open(org_altered_file_path) as ifile:
						with open(correctedfile_path, 'w') as ofile:
							for line in ifile:
								if '(assert (<= l' in line:
									corrected_line=line.replace(str(upperbound*10),str(upperbound*22));
									ofile.write(corrected_line);
								else:
									ofile.write(line);
					#remove original altered file
					if os.path.exists(org_altered_file_path):
					#{
						os.remove(org_altered_file_path);
					#}
				#}
			#}
		#}
	#}
	elif ((os.path.isdir(batch_folder_path)) and (('batchlength50000' not in program) or ('batchlength100000' not in program) or ('batchlength200000' not in program))):#correct only the filenames
	#{
		#for each smt file in this folder that does not have a filename that contain 'from0_to' or 'from100_to' or 'from200_to' #because these files were corrected manually
		files=os.listdir(batch_folder_path);
		for file in files:
		#{
			#if (('.smt2' in file) and ('from0_to' not in file) and ('from100_to' not in file) and ('from200_to' not in file)):
			#above if not needed because 'assert(<= l' occurs only in upperbound constraint, so this value gets replaced on in those constraints
			if ('.smt2' in file): #correct names of all smt files
			#{
				org_altered_file_path=os.path.join(batch_folder_path,file);
				correctedfile=file.replace('.smt2_from','_from');
				correctedfile=correctedfile.replace('.smt2_altered','_altered');
				correctedfile='nw_'+ correctedfile;
				correctedfile_path=os.path.join(batch_folder_path,correctedfile);
				with open(org_altered_file_path) as ifile:
					with open(correctedfile_path, 'w') as ofile:
						for line in ifile:
							ofile.write(line);
				#remove original altered file
				if os.path.exists(org_altered_file_path):
				#{
					os.remove(org_altered_file_path);
				#}
			#}
		#}
	#}
	else:
		pass
#}